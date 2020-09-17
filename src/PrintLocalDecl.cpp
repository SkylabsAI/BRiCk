/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "Logging.hpp"

using namespace clang;

class PrintLocalDecl :
    public ConstDeclVisitorArgs<PrintLocalDecl, bool, CoqPrinter&,
                                ClangPrinter&> {
private:
    PrintLocalDecl() {}

public:
    static PrintLocalDecl printer;

    bool VisitVarDecl(const VarDecl* decl, CoqPrinter& print,
                      ClangPrinter& cprint) {
        print.ctor("Build_VarDecl")
            << fmt::nbsp << "\"" << decl->getNameAsString() << "\""
            << fmt::nbsp;
        cprint.printQualType(decl->getType(), print);

        if (decl->hasInit()) {
            print.ctor("Some");
            cprint.printExpr(decl->getInit(), print);
            print.end_ctor();
        } else {
            print.none();
        }
        print.end_ctor();
        return true;
    }

    bool VisitTypeDecl(const TypeDecl* decl, CoqPrinter&,
                       ClangPrinter& cprint) {
        using namespace logging;
        debug() << "local type declarations are (currently) not well supported "
                << decl->getDeclKindName() << " (at "
                << cprint.sourceRange(decl->getSourceRange()) << ")\n";
        return false;
    }

    bool VisitStaticAssertDecl(const StaticAssertDecl* decl, CoqPrinter&,
                               ClangPrinter&) {
        return false;
    }

    bool VisitDecl(const Decl* decl, CoqPrinter& print, ClangPrinter& cprint) {
        using namespace logging;
        debug() << "unexpected local declaration while printing local decl "
                << decl->getDeclKindName() << " (at "
                << cprint.sourceRange(decl->getSourceRange()) << ")\n";
        return false;
    }
};

PrintLocalDecl PrintLocalDecl::printer;

bool
ClangPrinter::printLocalDecl(const clang::Decl* decl, CoqPrinter& print) {
    return PrintLocalDecl::printer.Visit(decl, print, *this);
}
