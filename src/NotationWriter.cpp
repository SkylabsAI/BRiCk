#include "ClangPrinter.hpp"
#include "CommentScanner.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/Version.inc"
#include <algorithm>

#if 0
// Ideally, we could use clang's [NamedDecl::printQualifiedName] function
// but this generates names that include spaces which doesn't work well
// with Coq's notation mechanism.
void
print_path(CoqPrinter &print, const DeclContext *dc, bool end = true) {
    if (dc == nullptr || isa<TranslationUnitDecl>(dc)) {
        if (end)
            print.output() << "::";
    } else {
        print_path(print, dc->getParent());
        if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(dc)) {
            print.output() << ts->getNameAsString() << "<";
            bool first = true;
            for (auto i : ts->getTemplateArgs().asArray()) {
                if (!first) {
                    print.output() << ",";
                }
                first = false;
                switch (i.getKind()) {
                case TemplateArgument::ArgKind::Integral:
                    print.output() << i.getAsIntegral();
                    break;
                case TemplateArgument::ArgKind::Type: {
                    auto s = i.getAsType().getAsString();
                    replace(s.begin(), s.end(), ' ', '_');
                    print.output() << s;
                    break;
                }
                default:
                    print.output() << "?";
                }
            }
            print.output() << (end ? ">::" : ">");
        } else if (auto td = dyn_cast<TagDecl>(dc)) {
            if (td->getName() != "") {
                print.output() << td->getNameAsString() << (end ? "::" : "");
            }
        } else if (auto ns = dyn_cast<NamespaceDecl>(dc)) {
            if (!ns->isAnonymousNamespace()) {
                print.output() << ns->getNameAsString() << (end ? "::" : "");
            }
        } else {
            using namespace logging;
            //logging::log() << "unknown declaration while printing path "
            //               << dc->getDeclKindName() << "\n";
        }
    }
}
#endif

/**
 * Print a human-readable name *without spaces*.
 *
 * This is useful for generating Coq notation.
 */
void
print_name(const NamedDecl *decl, CoqPrinter &print) {
    auto nm = decl->getQualifiedNameAsString();
    replace(nm.begin(), nm.end(), ' ', '_');
    // NOTE we need to print a leading '::' because if [nm]
    // is a single string, e.g. [Foo], then Coq will start
    // interpreting it as a keyword which is problematic.
    // This might be fixed with:
    //    https://github.com/coq/ceps/pull/41
    print.output() << "::" << nm;
}

void
write_globals(::Module &mod, CoqPrinter &print, ClangPrinter &cprint) {
    print.output() << "Module _'." << fmt::indent << fmt::line;

    // todo(gmm): i would like to generate function names.
    for (auto def : mod.definitions()) {
        if (const FieldDecl *fd = dyn_cast<FieldDecl>(def)) {
            print.output() << "Notation \"'";
            print_name(fd, print);
            //print_path(print, fd->getParent(), true);
            //fd->printName(print.output().nobreak());
            print.output() << "'\" :=" << fmt::nbsp;
            cprint.printField(fd, print);
            print.output() << " (in custom cppglobal at level 0)." << fmt::line;
        } else if (const RecordDecl *rd = dyn_cast<RecordDecl>(def)) {
            if (!rd->isAnonymousStructOrUnion() && rd->getIdentifier()) {

                print.output() << "Notation \"'";
                print_name(rd, print);
                //print_path(print, rd, false);
                //rd->printName(print.output().nobreak());
                print.output() << "'\" :=" << fmt::nbsp;

                cprint.printTypeName(rd, print);
                print.output()
                    << "%bs (in custom cppglobal at level 0)." << fmt::line;
            }

            for (auto fd : rd->fields()) {
                if (fd->getIdentifier()) {
                    print.output() << "Notation \"'";
                    print_name(fd, print);
                    //print_path(print, rd, true);
                    //fd->printQualifiedName(print.output().nobreak());
                    print.output() << "'\" :=" << fmt::nbsp;
                    cprint.printField(fd, print);
                    print.output()
                        << " (in custom cppglobal at level 0)." << fmt::line;
                }
            }
        } else if (const FunctionDecl *fd = dyn_cast<FunctionDecl>(def)) {
            // todo(gmm): skipping due to function overloading
        } else if (const TypedefDecl *td = dyn_cast<TypedefDecl>(def)) {
            print.output() << "Notation \"'";
            print_name(td, print);
            // print_path(print, td->getDeclContext(), true);
            //td->printQualifiedName(print.output().nobreak());
            print.output() << "'\" :=" << fmt::nbsp;
            cprint.printQualType(td->getUnderlyingType(), print);
            print.output() << " (in custom cppglobal at level 0)." << fmt::line;
        } else if (isa<VarDecl>(def) || isa<EnumDecl>(def) ||
                   isa<EnumConstantDecl>(def)) {
        } else if (auto ta = dyn_cast<TypeAliasDecl>(def)) {
            print.output() << "Notation \"'";
            print_name(ta, print);
            //def->printQualifiedName(print.output().nobreak());
            print.output() << "'\" :=" << fmt::nbsp;
            cprint.printQualType(ta->getUnderlyingType(), print);
            print.output() << " (in custom cppglobal at level 0)." << fmt::line;
        } else {
            using namespace logging;
            log(Level::VERBOSE) << "Unknown declaration type "
                                << def->getDeclKindName() << "\n";
        }
    }

    print.output() << fmt::outdent << "End _'." << fmt::line;
    print.output() << "Export _'." << fmt::line << fmt::line;
}