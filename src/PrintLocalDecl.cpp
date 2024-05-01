/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "OpaqueNames.hpp"
#include "clang/Frontend/CompilerInstance.h"

using namespace clang;

class PrintLocalDecl : public ConstDeclVisitorArgs<PrintLocalDecl, bool> {
public:
	PrintLocalDecl(CoqPrinter& print, ClangPrinter& cprint, OpaqueNames& names)
		: print(print), cprint(cprint), names(names) {}

private:
	CoqPrinter& print;
	ClangPrinter& cprint;
	OpaqueNames& names;

	CXXDestructorDecl* get_dtor(QualType qt) {
		if (auto rd = qt->getAsCXXRecordDecl()) {
			return rd->getDestructor();
		} else if (auto ary = qt->getAsArrayTypeUnsafe()) {
			return get_dtor(ary->getElementType());
		} else {
			return nullptr;
		}
	}

	void printDestructor(QualType qt) {
		// TODO when destructors move to classes, we can change this
		if (auto dest = get_dtor(qt)) {
			print.some();
			cprint.printName(*dest, print);
			print.end_ctor();
		} else {
			print.none();
		}
	}

public:
	bool VisitVarDecl(const VarDecl* decl) {
		// TODO: The following seems to be unsupported by parser.v
		if (decl->isStaticLocal()) {
			bool thread_safe =
				cprint.getCompiler().getLangOpts().ThreadsafeStatics;
			print.ctor("Dinit");
			print.output() << fmt::BOOL(thread_safe) << fmt::nbsp;
			cprint.printName(*decl, print);
			print.output() << fmt::nbsp;
		} else {
			print.ctor("Dvar")
				<< "\"" << decl->getNameAsString() << "\"" << fmt::nbsp;
		}

		auto declty = decl->getType();
		cprint.printQualType(declty, print, loc::of(decl));
		print.output() << fmt::nbsp;

		if (auto init = decl->getInit()) {
			print.some();
			cprint.printExpr(init, print, names);
			print.end_ctor();
		} else {
			print.none();
		}

		print.end_ctor();
		return true;
	}

	bool VisitTypeDecl(const TypeDecl* decl) {
		using namespace logging;
		debug() << "local type declarations are (currently) not well supported "
				<< decl->getDeclKindName() << " (at "
				<< cprint.sourceRange(decl->getSourceRange()) << ")\n";
		return false;
	}

	bool VisitStaticAssertDecl(const StaticAssertDecl* decl) {
		return false;
	}

	bool VisitDecl(const Decl* decl) {
		using namespace logging;
		debug() << "unexpected local declaration while printing local decl "
				<< decl->getDeclKindName() << " (at "
				<< cprint.sourceRange(decl->getSourceRange()) << ")\n";
		return false;
	}

	bool VisitDecompositionDecl(const DecompositionDecl* decl) {
		print.ctor("Ddecompose");

		cprint.printExpr(decl->getInit(), print, names);

		int index = names.push_anon(decl);
		print.output() << fmt::nbsp << "(localname.anon " << index << ")";

		print.output() << fmt::nbsp;

		print.list_filter(decl->bindings(), [&](const BindingDecl* b) {
			if (auto* var = b->getHoldingVar()) {
				Visit(var);
				return true;
			} else {
				decl->dump();
				llvm::errs().flush();
				always_assert(false && "no HoldingVar for declaration");
				return false;
				// NOTE: this code is copied from [VisitVarDecl].
				// We previously did:
				// [[
				//   this->Visit(b->getHoldingVar(), print, cprint, on);
				// ]]
				// But in certain instances, [getHoldingVar] returns a
				// [nullptr]. So we access the data directly from the [BindDecl].
			}
		});

		names.pop_anon(decl);

		print.end_ctor();
		return true;
	}
};

bool
ClangPrinter::printLocalDecl(const clang::Decl* decl, CoqPrinter& print) {
	if (trace(Trace::Local))
		trace("printLocalDecl", loc::of(decl));
	OpaqueNames names;
	return PrintLocalDecl{print, *this, names}.Visit(decl);
}
