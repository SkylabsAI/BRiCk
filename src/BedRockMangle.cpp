/*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/Basic/Version.h>
#include <clang/Frontend/CompilerInstance.h>
#include <optional>

/*
The mangler in this file is incomplete but handles a large
enough fragment of C++ to be useful in the short term.

NOTE: The existing ItaniumMangler does *almost* what we want
except it does not produce cross-translation unit unique names
for anonymous types which renders it largely unusable for
modular verification purposes.
 */

using namespace clang;

#if CLANG_VERSION_MAJOR >= 11
static GlobalDecl
to_gd(const NamedDecl *decl) {
    if (auto ct = dyn_cast<CXXConstructorDecl>(decl)) {
        return GlobalDecl(ct, CXXCtorType::Ctor_Complete);
    } else if (auto dt = dyn_cast<CXXDestructorDecl>(decl)) {
        return GlobalDecl(dt, CXXDtorType::Dtor_Deleting);
    } else {
        return GlobalDecl(decl);
    }
}
#else
static const NamedDecl *
to_gd(const NamedDecl *decl) {
    return decl;
}
#endif /* CLANG_VERSION_MAJOR >= 11 */

// #define CLANG_NAMES
#ifdef CLANG_NAMES
void
ClangPrinter::printTypeName(const TypeDecl *decl, CoqPrinter &print) const {
    std::string sout;
    llvm::raw_string_ostream out(sout);
    mangleContext_->mangleTypeName(QualType(decl->getTypeForDecl(), 0), out);
    out.flush();
    assert(3 < sout.length() && "mangled string length is too small");
    assert(sout.substr(0, 4) == "_ZTS");
    sout = sout.substr(4, sout.length() - 4);
    print.output() << "\"_Z" << sout << "\"";
}

#else /* CLANG_NAMES */
#ifdef STRUCTURED_NAMES
namespace {
unsigned
getAnonymousIndex(const NamedDecl *here) {
    auto i = 0;
    for (auto x : here->getDeclContext()->decls()) {
        if (x == here)
            return i;
        if (auto ns = dyn_cast<NamespaceDecl>(x)) {
            if (ns->isAnonymousNamespace())
                ++i;
        } else if (auto r = dyn_cast<RecordDecl>(x)) {
            if (r->getIdentifier() == nullptr)
                ++i;
        } else if (auto e = dyn_cast<EnumDecl>(x)) {
            if (e->getIdentifier() == nullptr)
                ++i;
        }
    }
    logging::fatal()
        << "Failed to find anonymous declaration in its own [DeclContext].\n"
        << here->getQualifiedNameAsString() << "\n";
    logging::die();
}
} // namespace

void
ClangPrinter::printTypeName(const TypeDecl *here, CoqPrinter &print) const {
    if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(here)) {
        print.ctor("Tspecialize");
        printTypeName(ts->getSpecializedTemplate(), print);
        print.output() << fmt::nbsp;
        auto &&args = ts->getTemplateArgs();
        print.begin_list();
        for (auto i = 0; i < args.size(); ++i) {
            auto &&arg = args[i];
            switch (arg.getKind()) {
            case TemplateArgument::ArgKind::Type:
                printQualType(arg.getAsType(), print);
                break;
            case TemplateArgument::ArgKind::Expression:
                printExpr(arg.getAsExpr(), print);
                break;
            case TemplateArgument::ArgKind::Integral:
                print.output() << arg.getAsIntegral().toString(10);
                break;
            case TemplateArgument::ArgKind::NullPtr:
                print.output() << "Enullptr";
                break;
            default:
                print.output() << "<else>";
            }
            print.cons();
        }
        print.end_list();
        print.end_ctor();
        return;
    }

    auto print_parent = [&](const DeclContext *parent) {
        if (auto pnd = dyn_cast<NamedDecl>(parent)) {
            printTypeName(pnd, print);
            print.output() << fmt::nbsp;
        } else {
            llvm::errs() << here->getDeclKindName() << "\n";
            assert(false && "unknown type in print_path");
        }
    };

    auto parent = here->getDeclContext();
    if (parent == nullptr or parent->isTranslationUnit()) {
        print.ctor("Qglobal", false);
        print.str(here->getName());
        print.end_ctor();
    } else if (auto nd = dyn_cast<NamespaceDecl>(here)) {
        print.ctor("Qnested", false);
        print_parent(parent);
        if (nd->isAnonymousNamespace() or nd->getIdentifier() == nullptr) {
            print.output() << "(Tanon " << getAnonymousIndex(nd) << ")";
        } else {
            print.str(here->getName());
        }
        print.end_ctor();
    } else if (auto rd = dyn_cast<RecordDecl>(here)) {
        print.ctor("Qnested", false);
        print_parent(parent);
        if (rd->getIdentifier() == nullptr) {
            print.output() << "(Tanon " << getAnonymousIndex(rd) << ")";
        } else {
            print.str(here->getName());
        }
        print.end_ctor();
    } else if (auto pnd = dyn_cast<NamedDecl>(parent)) {
        print.ctor("Qnested", false);
        printTypeName(pnd, print);
        print.output() << fmt::nbsp;
        print.str(here->getName());
        print.end_ctor();
    } else {
        llvm::errs() << here->getDeclKindName() << "\n";
        assert(false && "unknown type in print_path");
    }
}
#else /* STRUCTURED NAMES */

class StableMangler {
public:
    StableMangler(raw_ostream &_out, const ClangPrinter &cprint,
                  MangleContext &mangle)
        : out{_out}, cprint{cprint}, mangle_{mangle} {}
    void mangleType(const clang::Type *type);
    void mangleQualType(QualType t) {
        if (t.isConstQualified())
            out << "K";
        if (t.isVolatileQualified())
            out << "V";
        mangleType(t.getTypePtr());
    }
    unsigned manglePrefix(const clang::DeclContext *dc, unsigned remaining = 0);
    unsigned mangleNestedName(const NestedNameSpecifier *nns,
                              unsigned remaining = 0);
    void mangleName(const clang::NamedDecl *decl) {
        auto nested = manglePrefix(decl->getDeclContext(), 1);
        auto name = decl->getName();
        out << name.size() << name;
        finishName(nested);
    }
    void finishName(unsigned n) {
        if (1 < n)
            out << "E";
    }
    void mangleTemplateArg(clang::TemplateArgument targ) {
        switch (targ.getKind()) {
        case TemplateArgument::ArgKind::Type:
            mangleQualType(targ.getAsType());
            break;
        case TemplateArgument::ArgKind::Pack:
            out << "J";
            for (auto i : targ.pack_elements()) {
                mangleTemplateArg(i);
            }
            out << "E";
            break;
        case TemplateArgument::ArgKind::Integral:
            out << "L";
            mangleQualType(targ.getIntegralType());
            out << targ.getAsIntegral();
            out << "E";
            break;
        case TemplateArgument::ArgKind::NullPtr:
            out << "LDnE";
            break;
        case TemplateArgument::ArgKind::Expression:
            mangleExpr(targ.getAsExpr());
            break;
        default:
            out << "?";
            logging::unsupported()
                << "template argument " << targ.getKind() << "\n";
            break;
        }
    }
    void mangleUnOp(UnaryOperator::Opcode code) {
        switch (code) {
#define CASE(E, S)                                                             \
    case UnaryOperator::Opcode::UO_##E:                                        \
        out << #S;                                                             \
        break;
            CASE(AddrOf, ad)
            CASE(Coawait, aw)
            CASE(Deref, de)
            CASE(Minus, ng)
            CASE(Not, co)
            CASE(LNot, nt)
        default:
            logging::unsupported() << "mangle unary operator "
                                   << UnaryOperator::getOpcodeStr(code) << "\n";
            out << "?";
            break;
#undef CASE
        }
    }
    void mangleBinOp(BinaryOperator::Opcode code) {
        switch (code) {
#define CASE(E, S)                                                             \
    case BinaryOperator::Opcode::BO_##E:                                       \
        out << #S;                                                             \
        break;
            CASE(Add, pl)
            CASE(AddAssign, pL)
            CASE(And, an)
            CASE(AndAssign, aN)
            CASE(LAnd, aa)
            CASE(Sub, mi)
            CASE(Shl, ls)
            CASE(Shr, rs)
            CASE(Div, dv)
            CASE(Cmp, ss)
            CASE(Comma, cm)
            CASE(Assign, aS)
            CASE(Rem, rm)
            CASE(RemAssign, rM)
            CASE(Or, or)
            CASE(OrAssign, oR)
            CASE(LOr, oo)
#undef CASE
        default:
            logging::unsupported()
                << "mangle binary operator "
                << BinaryOperator::getOpcodeStr(code) << "\n";
            out << "?";
            break;
        }
    }
    void mangleExpr(const clang::Expr *expr) {
        mangleExpr_(expr, true);
    }

    bool mangleExpr_(const clang::Expr *expr, bool top = false) {
        // simple expressions
        if (auto il = dyn_cast<IntegerLiteral>(expr)) {
            out << "L";
            mangleQualType(il->getType());
            out << il->getValue();
            out << "E";
            return false;
        }

        // complex expressions are bracketed by X..E
        if (top)
            out << "X";
        if (auto bop = dyn_cast<BinaryOperator>(expr)) {
            mangleBinOp(bop->getOpcode());
            mangleExpr_(bop->getLHS());
            mangleExpr_(bop->getRHS());
        } else if (auto uop = dyn_cast<UnaryOperator>(expr)) {
            mangleUnOp(uop->getOpcode());
            mangleExpr_(uop->getSubExpr());
        } else if (auto dr = dyn_cast<DeclRefExpr>(expr)) {
            mangleName(dr->getDecl());
        } else {
            logging::unsupported()
                << "mangle expression " << expr->getStmtClassName() << "\n";
            out << "?";
        }
        if (top)
            out << "E";
        return true;
    }

protected:
    MangleContext &mangler() {
        return mangle_;
    }

private:
    raw_ostream &out;
    const ClangPrinter &cprint;
    MangleContext &mangle_;
};

void
StableMangler::mangleType(const clang::Type *type) {
    if (auto rt = dyn_cast<ReferenceType>(type)) {
        out << (isa<LValueReferenceType>(rt) ? "R" : "O");
        mangleQualType(rt->getPointeeType());
    } else if (auto pt = dyn_cast<PointerType>(type)) {
        out << "P";
        mangleQualType(pt->getPointeeType());
    } else if (auto ttp = dyn_cast<TemplateTypeParmType>(type)) {
        out << "TL";
        if (ttp->getDepth())
            out << ttp->getDepth() - 1;
        out << "_";
        if (ttp->getIndex())
            out << ttp->getIndex() - 1;
        out << "_";
    } else if (auto rt = dyn_cast<RecordType>(type)) {
        mangleName(rt->getDecl());
    } else if (auto bt = dyn_cast<BuiltinType>(type)) {
        switch (bt->getKind()) {
#define CASE(EN, C)                                                            \
    case BuiltinType::Kind::EN:                                                \
        out << #C;                                                             \
        break;
            CASE(NullPtr, Dn)
            CASE(Void, v)
            CASE(Char8, Du)
            CASE(Char16, Ds)
            CASE(Char32, Di)
            CASE(WChar_S, w)
            CASE(WChar_U, w)
            CASE(Char_S, c)
            CASE(Char_U, c)
            CASE(UChar, h)
            CASE(SChar, a)
            CASE(Short, s)
            CASE(UShort, t)
            CASE(Int, i)
            CASE(UInt, j)
            CASE(Long, l)
            CASE(ULong, m)
            CASE(LongLong, x)
            CASE(ULongLong, y)
            CASE(Bool, b)
            CASE(Float, f)
            CASE(Double, d)
            CASE(LongDouble, e)
        default:
            logging::unsupported() << "unsupported type for mangling\n";
            type->dump();
            out << "?"; // TODO: incomplete
        }
    } else if (auto tst = dyn_cast<TemplateSpecializationType>(type)) {
        auto name = tst->getTemplateName();
        if (auto td = name.getAsTemplateDecl()) {
            auto nested = manglePrefix(td->getDeclContext());

            out << "I";
            for (auto i : tst->template_arguments()) {
                mangleTemplateArg(i);
            }
            out << "E";

            finishName(nested);
        }
    } else if (auto at = dyn_cast<ArrayType>(type)) {
        out << "A";
        if (auto cat = dyn_cast<ConstantArrayType>(at)) {
            out << cat->getSize();
        } else if (auto dsat = dyn_cast<DependentSizedArrayType>(at)) {
            mangleExpr(dsat->getSizeExpr());
        } else if (auto iat = dyn_cast<IncompleteArrayType>(at)) {
            // the size is omitted for incomplete array types
        } else {
            out << "?";
        }
        out << "_";
        mangleQualType(at->getElementType());
    } else if (auto mpt = dyn_cast<MemberPointerType>(type)) {
        out << "M";
        mangleType(mpt->getClass());
        mangleQualType(mpt->getPointeeType());
    } else if (auto ft = dyn_cast<FunctionProtoType>(type)) {
        if (ft->isConst())
            out << "K";
        if (ft->isVolatile())
            out << "V";
        out << "F";
        mangleQualType(ft->getReturnType());
        for (auto p : ft->getParamTypes()) {
            mangleQualType(p);
        }
        if (ft->isVariadic())
            out << "z";
        out << "E";
    } else if (auto pet = dyn_cast<PackExpansionType>(type)) {
        out << "Dp";
        mangleQualType(pet->getPattern());
    } else if (auto et = dyn_cast<EnumType>(type)) {
        mangleName(et->getDecl());
    } else {
        logging::unsupported() << "unsupported type for mangling "
                               << type->getTypeClassName() << "\n";
        out << "?"; // TODO: incomplete
    }
}

unsigned
StableMangler::mangleNestedName(const NestedNameSpecifier *nns,
                                unsigned remaining) {
    switch (nns->getKind()) {
    case NestedNameSpecifier::SpecifierKind::Global:
        out << (1 < remaining ? "N" : "");
        return 0;
    case NestedNameSpecifier::SpecifierKind::Namespace: {
        auto ns = nns->getAsNamespace();
        auto nested = mangleNestedName(
            nns->getPrefix(), remaining + (ns->isAnonymousNamespace() ? 0 : 1));
        if (not ns->isAnonymousNamespace()) {
            auto name = nns->getAsNamespace()->getName();
            out << name.size() << name;
            nested++;
        }
        return nested;
    }
    case NestedNameSpecifier::SpecifierKind::NamespaceAlias: {
        auto ns = nns->getAsNamespaceAlias()->getNamespace();
        return manglePrefix(ns, remaining);
    }
    case NestedNameSpecifier::SpecifierKind::TypeSpec:
    case NestedNameSpecifier::SpecifierKind::TypeSpecWithTemplate: {
        auto type = nns->getAsType();
        // TODO: does this need to print the template?
        return manglePrefix(type->getAsTagDecl(), remaining);
    }
    default:
        logging::unsupported()
            << "Unsupported nested name " << nns->getKind() << "\n";
        out << "?";
        return 1;
    }
}

// returns the number of components that it printed
unsigned
StableMangler::manglePrefix(const DeclContext *dc, unsigned remaining) {
    if (dc == nullptr or dc->isTranslationUnit()) {
        out << (1 < remaining ? "N" : "");
        return 0;
    } else if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(dc)) {
        auto parent = ts->getDeclContext();
        auto compound = manglePrefix(parent, remaining + 1);
        auto name = ts->getName();
        out << name.size() << name << "I";
        for (auto arg : ts->getTemplateArgs().asArray()) {
            mangleTemplateArg(arg);
        }
        out << "E";
        return compound + 1;
#if 0
        if (auto dtor = ts->getDestructor()) {
            // HACK: this mangles an aggregate name by mangling
            // the destructor and then doing some string manipulation
            std::string sout;
            llvm::raw_string_ostream out(sout);
            mangle.mangleName(to_gd(dtor), out);
            out.flush();
            assert(3 < sout.length() && "mangled string length is too small");
            sout =
                sout.substr(0, sout.length() - 4); // cut off the final 'DnEv'
            if (not ts->getDeclContext()->isTranslationUnit() or
                0 < remaining) {
                print.output() << sout << (remaining == 0 ? "E" : "");
                return 2; // we approximate the whole string by 2
            } else {
                print.output() << "_Z" << sout.substr(3, sout.length() - 3);
                return 1;
            }
        } else {
            logging::debug()
                << "ClassTemplateSpecializationDecl not supported for "
                   "simple contexts.\n";
            static_cast<const clang::NamedDecl *>(ts)->printName(
                logging::debug());
            logging::debug() << "\n";
            ts->printQualifiedName(print.output().nobreak());
            return true;
        }
#endif
    } else if (auto ns = dyn_cast<NamespaceDecl>(dc)) {
        auto parent = ns->getDeclContext();
        auto compound = manglePrefix(parent, remaining + 1);
        if (not ns->isAnonymousNamespace()) {
            auto name = ns->getNameAsString();
            out << name.length() << name;
        } else if (not ns->decls_empty()) {
            // a proposed scheme is to use the name of the first declaration.
            out << "~<TODO>";
            // TODO
            // ns->field_begin()->printName(print.output().nobreak());
        } else {
            out << "~<empty>";
            logging::unsupported()
                << "empty anonymous namespaces are not supported."
                << " (at " << cprint.sourceRange(ns->getSourceRange()) << ")\n";
        }
        return compound + 1;
    } else if (auto rd = dyn_cast<RecordDecl>(dc)) {
        // NOTE: this occurs when you have a forward declaration,
        // e.g. [struct C;], or when you have a compiler builtin.
        // We need to mangle the name, but we can't really get any help
        // from clang.

        auto parent = rd->getDeclContext();
        auto compound = manglePrefix(parent, remaining + 1);
        if (rd->getIdentifier()) {
            auto name = rd->getName();
            out << name.size() << name;
        } else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
            auto s = tdn->getName();
            out << s.size() << s;
            //tdn->printName(print.output().nobreak());
        } else if (not rd->field_empty()) {
            out << ".";
            rd->field_begin()->printName(out);
        } else {
            // TODO this isn't technically sound
            out << "~<empty>";
            logging::unsupported()
                << "empty anonymous records are not supported. (at "
                << cprint.sourceRange(rd->getSourceRange()) << ")\n";
        }
        if (auto cxx_rd = dyn_cast<CXXRecordDecl>(dc)) {
            if (auto params = cxx_rd->getDescribedTemplateParams()) {
                // this follows the mangling from
                // https://github.com/itanium-cxx-abi/cxx-abi/issues/31#issuecomment-528122117
                out << "I";
                for (unsigned i = 0; i < params->size(); ++i) {
                    out << "TL";
                    if (params->getDepth())
                        out << params->getDepth() - 1;
                    out << "_";
                    if (i)
                        out << i - 1;
                    out << "_";
                }
                out << "E";
            }
        }
        return compound + 1;
    } else if (auto ed = dyn_cast<EnumDecl>(dc)) {
        auto parent = ed->getDeclContext();
        auto compound = manglePrefix(parent, remaining + 1);
        if (ed->getIdentifier()) {
            auto name = ed->getName();
            out << name.size() << name;
            //} else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
            //    llvm::errs() << "typedef name not null " << tdn << "\n";
            //    tdn->printName(out.nobreak());
        } else if (auto tdn = ed->getTypedefNameForAnonDecl()) {
            auto name = tdn->getName();
            out << name.size() << name;
        } else {
            if (ed->enumerators().empty()) {
                // no idea what to do
                out << "~<empty-enum>";
                logging::unsupported()
                    << "empty anonymous namespaces are not supported."
                    << " (at " << cprint.sourceRange(ed->getSourceRange())
                    << ")\n";
            } else {
                out << "~";
                ed->enumerators().begin()->printName(out);
            }
        }
        return compound + 1;
    } else if (auto fd = dyn_cast<FunctionDecl>(dc)) {
        std::string sout;
        llvm::raw_string_ostream out(sout);
        mangle_.mangleName(to_gd(fd), out);
        out.flush();
        assert(3 < sout.length() && "mangled string length is too small");
        if (not fd->getDeclContext()->isTranslationUnit()) {
            return 2; // we approximate the whole string by 2
        } else {
            out << sout;
            return 1;
        }
    } else if (auto ls = dyn_cast<LinkageSpecDecl>(dc)) {
        auto parent = ls->getDeclContext();
        return manglePrefix(parent, remaining);
    } else {
        logging::fatal() << "Unknown type (" << dc->getDeclKindName()
                         << ") in [printSimpleContext]\n";
        logging::die();
    }
}

void
ClangPrinter::printTypeName(const TypeDecl *decl, CoqPrinter &print) const {
    StableMangler mangle{print.output().nobreak(), *this, *mangleContext_};
    if (isa<RecordDecl>(decl) and not isa<CXXRecordDecl>(decl)) {
        // NOTE: this only matches C records, not C++ records
        // therefore, we do not perform any mangling.
        logging::debug() << "RecordDecl: " << decl->getQualifiedNameAsString()
                         << "\n";
        print.output() << "\"";
        decl->printQualifiedName(print.output().nobreak());
        print.output() << "\"";
    } else if (auto TD = dyn_cast<TagDecl>(decl)) {
        print.output() << "\"_Z";
        mangle.mangleName(TD);
        print.output() << "\"";
    } else {
        using namespace logging;
        fatal() << "Unknown decl kind to [printTypeName]: "
                << decl->getQualifiedNameAsString() << " "
                << decl->getDeclKindName() << "\n";
        die();
    }
}
#endif /* STRUCTURED_NAMES */
#endif /* CLANG_NAMES */

void
ClangPrinter::printObjName(const ValueDecl *decl, CoqPrinter &print, bool raw) {
    assert(!raw && "printing raw object names is no longer supported");

    // All enumerations introduce types, but only some of them have names.
    // While positional names work in scoped contexts, they generally
    // do not work in extensible contexts (e.g. the global context)
    //
    // To address this, we use the name of their first declation.
    // To avoid potential clashes (since the first declaration might be
    // a term name and not a type name), we prefix the symbol with a dot,
    // e.g.
    // [enum { X , Y , Z };] -> [.X]
    // note that [MangleContext::mangleTypeName] does *not* follow this
    // strategy.

    if (auto ecd = dyn_cast<EnumConstantDecl>(decl)) {
        // While they are values, they are not mangled because they do
        // not end up in the resulting binary. Therefore, we need a special
        // case.
        auto ed = dyn_cast<EnumDecl>(ecd->getDeclContext());
        print.ctor("Cenum_const", false);
        printTypeName(ed, print);
        print.output() << " \"";
        ecd->printName(print.output().nobreak());
        print.output() << "\"";
        print.end_ctor();
    } else if (auto dd = dyn_cast<CXXDestructorDecl>(decl)) {
        // NOTE we implement our own destructor mangling because
        // we are not guaranteed to be able to generate the
        // destructor for every aggregate and our current setup requires
        // that all aggregates have named destructors.
        //
        // An alternative (cleaner) solution is to extend the type
        // of names to introduce a distinguished name for destructors.
        // Doing this is a bit more invasive.
        print.ctor("DTOR", false);
        printTypeName(dd->getParent(), print);
        print.end_ctor();
    } else if (mangleContext_->shouldMangleDeclName(decl)) {
        print.output() << "\"";
        mangleContext_->mangleName(to_gd(decl), print.output().nobreak());
        print.output() << "\"";
    } else {
        print.output() << "\"";
        decl->printName(print.output().nobreak());
        print.output() << "\"";
    }
}

void
ClangPrinter::printName(const NamedDecl *decl, CoqPrinter &print) {
    if (auto ctd = dyn_cast<ClassTemplateDecl>(decl)) {
        return printName(ctd->getTemplatedDecl(), print);
    } else if (auto vd = dyn_cast<ValueDecl>(decl)) {
        return printObjName(vd, print);
    } else if (auto td = dyn_cast<TypeDecl>(decl)) {
        printTypeName(td, print);
#if 0
        print.output() << "\"";
        mangleContext_->mangleTypeName(QualType{td->getTypeForDecl(), 0},
                                       print.output().nobreak());
        print.output() << "\"";
    } else if (auto dc = dyn_cast<TagDecl>(decl)) {
        print.output() << "\"_Z";
        StableMangler{print.output().nobreak(), *this, *mangleContext_}
            .mangleName(decl->getDeclContext());
        print.output() << "\"";
#endif
    } else {
        llvm::errs() << "default printer for " << decl->getDeclKindName()
                     << "\n";
        // TODO: this is not consistent with
        print.output() << "\"_Z";
        auto nested =
            StableMangler{print.output().nobreak(), *this, *mangleContext_}
                .manglePrefix(decl->getDeclContext(), 1);
        auto name = decl->getName();
        print.output() << name.size() << name;
        if (nested) {
            print.output() << "E";
        }
        print.output() << "\"";
    }
}
