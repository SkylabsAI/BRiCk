/*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "ToGd.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/Basic/Version.h>
#include <clang/Frontend/CompilerInstance.h>

using namespace clang;

/*
 * This file approximates a "mangler" the should assign stable names to all types.
 * This is necessary so that we can translate a header file and a source file
 * separately and the header will be a submodule of the source file without needing
 * to compute an isomorphism.
 * We can *not* use the builtin manglers because they generate names for anonymous
 * types using integers that are not stable.
 * 
 * In the future, we will probably want to copy the ItaniumMangler and modify the
 * way that it mangles anonymous names. Doing this will give us better support for
 * features such as lambdas.
 */

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

/*
 * NOTE that this implementation is buggy because it does not use a mangling
 * context correctly. To fix this, we need to build a more complete mangler.
 */

// returns the number of components that it printed
size_t printSimpleContext(const DeclContext *dc, CoqPrinter &print,
                          const ClangPrinter &cprint, MangleContext &mangle,
                          size_t remaining = 0);

size_t
printTypeName(const TypeDecl *decl, CoqPrinter &print,
              const ClangPrinter &cprint, MangleContext &mangle) {
    if (auto RD = dyn_cast<CXXRecordDecl>(decl)) {
        return printSimpleContext(RD, print, cprint, mangle);
    } else if (auto rd = dyn_cast<RecordDecl>(decl)) {
        // NOTE: this only matches C records, not C++ records
        // therefore, we do not perform any mangling.
        logging::debug() << "RecordDecl: " << decl->getQualifiedNameAsString()
                         << "\n";
        decl->printQualifiedName(print.output().nobreak());
        return 1;
    } else if (auto ed = dyn_cast<EnumDecl>(decl)) {
        return printSimpleContext(ed, print, cprint, mangle);
    } else {
        using namespace logging;
        fatal() << "Unknown decl kind to [printTypeName]: "
                << decl->getQualifiedNameAsString() << " "
                << decl->getDeclKindName() << "\n";
        die();
    }
}

char
manglePrimitive(QualType qt) {
    if (auto bt = dyn_cast<BuiltinType>(qt.getTypePtr())) {
        switch (bt->getKind()) {
#define CASE(X, c)                                                             \
    case BuiltinType::Kind::X:                                                 \
        return '#c';
            CASE(Bool, b)
            CASE(UChar, h)
            CASE(Char_U, h)
            CASE(Char8, c)
            CASE(SChar, a)
            CASE(Char_S, a)
            CASE(UShort, t)
            CASE(Short, s)
            CASE(Int, i)
            CASE(UInt, j)
            CASE(Long, l)
            CASE(ULong, m)
            CASE(LongLong, x)
            CASE(ULongLong, y)
            CASE(Void, v)
            CASE(Float, f)
            CASE(Double, d)
#undef CASE
        default:
            logging::unsupported()
                << "unsupported mangling for builtin: " << bt->getKind()
                << "\r\n";
            return '?';
        }
    }
}

size_t
printSimpleContext(const DeclContext *dc, CoqPrinter &print,
                   const ClangPrinter &cprint, MangleContext &mangle,
                   size_t remaining) {
    if (dc == nullptr or dc->isTranslationUnit()) {
        print.output() << (1 < remaining ? "N" : "");
        return 0;
    } else if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(dc)) {
        auto compound =
            printSimpleContext(ts->getSpecializedTemplate()->getDeclContext(),
                               print, cprint, mangle, remaining + 1);
        std::string nm;
        llvm::raw_string_ostream sout{nm};

        ts->printName(sout);
        sout.flush();
        print.output() << nm.length() << nm << "I";
        auto &args = ts->getTemplateArgs();
        for (auto i = 0; i < args.size(); ++i) {
            auto &arg = args[i];
            switch (arg.getKind()) {
            case TemplateArgument::ArgKind::Declaration:
                // NOTE: I can not call the mangler on the declaration because
                // it will use a fresh mangling context.
                logging::unsupported() << "unsupported mangling for template "
                                          "parameter: declaration";
                print.output() << "?";
                break;
            case TemplateArgument::ArgKind::Integral:
                print.output() << "L" << manglePrimitive(arg.getIntegralType())
                               << arg.getAsIntegral() << "E";
                break;
            case TemplateArgument::ArgKind::NullPtr:
                print.output() << "Dn";
                break;
            case TemplateArgument::ArgKind::Type: {
                auto qt = arg.getAsType();
                if (auto tag = qt.getTypePtr()->getAsTagDecl()) {
                    printTypeName(arg.getAsType().getTypePtr()->getAsTagDecl(),
                                  print, cprint, mangle);
                } else if (auto bt = dyn_cast<BuiltinType>(qt.getTypePtr())) {
                    manglePrimitive(qt);
                }
                break;
            }
            default:
                logging::unsupported()
                    << "unsupported mangling for template parameter: "
                    << args[i].getKind() << "\r\n";
                print.output() << "?(arg:" << args[i].getKind() << ")";
            }
        }

        print.output() << "E";
        return compound + 1;
    } else if (auto ns = dyn_cast<NamespaceDecl>(dc)) {
        auto compound = printSimpleContext(ns->getDeclContext(), print, cprint,
                                           mangle, remaining + 1);
        if (not ns->isAnonymousNamespace()) {
            auto name = ns->getNameAsString();
            print.output() << name.length() << name;
        } else if (not ns->decls_empty()) {
            // a proposed scheme is to use the name of the first declaration.
            print.output() << "~<TODO>";
            // TODO
            // ns->field_begin()->printName(print.output().nobreak());
        } else {
            print.output() << "~<empty>";
            logging::unsupported()
                << "empty anonymous namespaces are not supported."
                << " (at " << cprint.sourceRange(ns->getSourceRange()) << ")\n";
        }
        if (remaining == 0 && 0 < compound)
            print.output() << "E";
        return compound + 1;
    } else if (auto rd = dyn_cast<RecordDecl>(dc)) {
        // NOTE: this occurs when you have a forward declaration,
        // e.g. [struct C;], or when you have a compiler builtin.
        // We need to mangle the name, but we can't really get any help
        // from clang.

        auto compound = printSimpleContext(rd->getDeclContext(), print, cprint,
                                           mangle, remaining + 1);
        if (rd->getIdentifier()) {
            auto name = rd->getNameAsString();
            print.output() << name.length() << name;
        } else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
            auto s = tdn->getNameAsString();
            print.output() << s.length() << s;
            //tdn->printName(print.output().nobreak());
        } else if (not rd->field_empty()) {
            print.output() << ".";
            rd->field_begin()->printName(print.output().nobreak());
        } else {
            // TODO this isn't technically sound
            print.output() << "~<empty>";
            logging::unsupported()
                << "empty anonymous records are not supported. (at "
                << cprint.sourceRange(rd->getSourceRange()) << ")\n";
        }
        return compound + 1;
    } else if (auto ed = dyn_cast<EnumDecl>(dc)) {
        auto parent = ed->getDeclContext();
        auto compound =
            printSimpleContext(parent, print, cprint, mangle, remaining + 1);
        if (ed->getIdentifier()) {
            auto name = ed->getNameAsString();
            print.output() << name.length() << name;
            //} else if (auto tdn = rd->getTypedefNameForAnonDecl()) {
            //    llvm::errs() << "typedef name not null " << tdn << "\n";
            //    tdn->printName(print.output().nobreak());
        } else {
            if (ed->enumerators().empty()) {
                // no idea what to do
                print.output() << "~<empty-enum>";
                logging::unsupported()
                    << "empty anonymous namespaces are not supported."
                    << " (at " << cprint.sourceRange(ed->getSourceRange())
                    << ")\n";
            } else {
                print.output() << "~";
                ed->enumerators().begin()->printName(print.output().nobreak());
            }
        }
        return compound + 1;
    } else if (auto fd = dyn_cast<FunctionDecl>(dc)) {
        std::string sout;
        llvm::raw_string_ostream out(sout);
        mangle.mangleName(to_gd(fd), out);
        out.flush();
        assert(3 < sout.length() && "mangled string length is too small");
        if (not fd->getDeclContext()->isTranslationUnit()) {
            print.output() << sout << (remaining == 0 ? "E" : "");
            return 2; // we approximate the whole string by 2
        } else {
            print.output() << sout;
            return 1;
        }
    } else if (auto ls = dyn_cast<LinkageSpecDecl>(dc)) {
        auto parent = ls->getDeclContext();
        return printSimpleContext(parent, print, cprint, mangle, remaining);
    } else {
        logging::fatal() << "Unknown type (" << dc->getDeclKindName()
                         << ") in [printSimpleContext]\n";
        logging::die();
    }
}

void
ClangPrinter::printTypeName(const TypeDecl *decl, CoqPrinter &print) const {
    print.output() << "\"_Z";
    if (1 < ::printTypeName(decl, print, *this, *mangleContext_)) {
        print.output() << "E";
    }
    print.output() << "\"";
}
#endif /* STRUCTURED_NAMES */
#endif /* CLANG_NAMES */
