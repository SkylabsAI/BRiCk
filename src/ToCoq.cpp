/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CommentScanner.hpp"
#include "CoqPrinter.hpp"
#include "Filter.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Type.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>
#include <list>

#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"

// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"

#include "SpecCollector.hpp"
#include "ToCoq.hpp"

using namespace clang;
using namespace fmt;

template<typename CLOSURE>
void
with_open_file(const std::optional<std::string> path,
			   CLOSURE f /* void f(Formatter&) */) {
	if (path.has_value()) {
		std::error_code ec;
		llvm::raw_fd_ostream output(*path, ec);
		if (ec.value()) {
			llvm::errs() << *path << ": " << ec.message() << "\n";
		} else {
			Formatter fmt{output};
			f(fmt);
		}
	}
}

void
printDecl(const clang::Decl* decl, CoqPrinter& print, ClangPrinter& cprint) {
	if (cprint.printDecl(decl, print))
		print.cons();
}

namespace name_test {
static void
bug(ClangPrinter& cprint, loc::loc loc, const std::string what) {
	cprint.error_prefix(logging::fatal(), loc) << "BUG: " << what << "\n";
	cprint.debug_dump(loc);
	logging::die();
}

static void
test(const clang::Decl* decl, CoqPrinter& print, ClangPrinter& cprint) {
	if (decl && decl->isImplicit() && isa<TypedefDecl>(decl))
		// Suppress clang's implicit typedefs
		return;
	else if (decl) {
		print.output() << fmt::line;
		std::string cmt;
		llvm::raw_string_ostream os{cmt};
		os << loc::trace(loc::of(decl), cprint.getContext());
		print.cmt(cmt) << fmt::nbsp;
		cprint.printName(*decl, print);
		print.output() << " ::" << fmt::line;
	} else
		bug(cprint, loc::none, "null declaration");
}
}

void
ToCoqConsumer::toCoqModule(clang::ASTContext* ctxt,
						   clang::TranslationUnitDecl* decl) {

#if 0
	NoInclude noInclude(ctxt->getSourceManager());
	FromComment fromComment(ctxt);
	std::list<Filter*> filters;
	filters.push_back(&noInclude);
	filters.push_back(&fromComment);
	Combine<Filter::What::NOTHING, Filter::max> filter(filters);
#endif
	SpecCollector specs;
	Default filter(Filter::What::DEFINITION);

	::Module mod(trace_);

	bool templates = templates_file_.has_value() || name_test_file_.has_value();
	build_module(decl, mod, filter, specs, compiler_, elaborate_, templates);

	auto parser = [&](CoqPrinter& print) -> auto& {
		StringRef coqmod(print.templates() ?
							 "bedrock.auto.cpp.templates.mparser2" :
							 "bedrock.lang.cpp.parser2");
		return print.output()
			   << "Require Import " << coqmod << "." << fmt::line << fmt::line;
	};

	auto bytestring = [&](CoqPrinter& print) -> auto& {
		return print.output() << "#[local] Open Scope bs_scope." << fmt::line;
	};

	with_open_file(output_file_, [&](Formatter& fmt) {
		CoqPrinter print(fmt, /*templates*/ false, structured_keys_);
		ClangPrinter cprint(compiler_, ctxt, trace_, comment_);

		parser(print);
		bytestring(print) << fmt::line;

		print.output()
			<< "Definition module : translation_unit := " << fmt::indent
			<< fmt::line
			<< "Eval reduce_translation_unit in translation_unit.decls"
			<< fmt::nbsp;

		print.begin_list();
		for (auto decl : mod.declarations()) {
			printDecl(decl, print, cprint);
		}
		for (auto decl : mod.definitions()) {
			printDecl(decl, print, cprint);
		}
		for (auto decl : mod.asserts()) {
			printDecl(decl, print, cprint);
		}
		print.end_list();
		print.output() << fmt::nbsp;
		if (ctxt->getTargetInfo().isBigEndian()) {
			print.output() << "Big";
		} else {
			always_assert(ctxt->getTargetInfo().isLittleEndian());
			print.output() << "Little";
		}

		// TODO I still need to generate the initializer

		print.output() << "." << fmt::outdent << fmt::line;
	});

	with_open_file(notations_file_, [&](Formatter& spec_fmt) {
		auto& ctxt = decl->getASTContext();
		CoqPrinter print(spec_fmt, /*templates*/ false, structured_keys_);
		ClangPrinter cprint(compiler_, &ctxt, trace_, comment_);
		// PrintSpec printer(ctxt);

		NoInclude source(ctxt.getSourceManager());

		// print.output() << "(*" << fmt::line
		//                << " * Notations extracted from "
		//                << ctxt.getSourceManager()
		//                       .getFileEntryForID(
		//                           ctxt.getSourceManager().getMainFileID())
		//                       ->getName()
		//                << fmt::line << " *)" << fmt::line;

		parser(print);

		// generate all of the record fields
		write_globals(mod, print, cprint);
	});

	with_open_file(templates_file_, [&](Formatter& fmt) {
		CoqPrinter print(fmt, /*templates*/ true, structured_keys_);
		ClangPrinter cprint(compiler_, ctxt, trace_, comment_);

		parser(print);
		bytestring(print) << fmt::line;

		print.output()
			<< "Definition templates : Mtranslation_unit :=" << fmt::indent
			<< fmt::line
			<< "Eval reduce_translation_unit in Mtranslation_unit.decls"
			<< fmt::nbsp;

		print.begin_list();
		for (auto decl : mod.template_declarations()) {
			printDecl(decl, print, cprint);
		}
		for (auto decl : mod.template_definitions()) {
			printDecl(decl, print, cprint);
		}
		print.end_list();

		print.output() << "." << fmt::outdent << fmt::line;
	});

	with_open_file(name_test_file_, [&](Formatter& fmt) {
		CoqPrinter print(fmt, /*templates*/ true, /*structured_keys*/ true);
		ClangPrinter cprint(compiler_, ctxt, trace_, comment_);

		auto testnames = [&](const std::string id,
							 std::function<void()> k) -> auto& {
			print.output() << fmt::line << "Definition " << id
						   << " : list Mname :=" << fmt::indent << fmt::line;
			print.begin_list();
			k();
			print.end_list();
			return print.output() << "." << fmt::outdent << fmt::line;
		};

		parser(print);
		bytestring(print);

		testnames("module_names", [&]() {
			for (auto decl : mod.declarations()) {
				name_test::test(decl, print, cprint);
			}
			for (auto decl : mod.definitions()) {
				name_test::test(decl, print, cprint);
			}
		});
		testnames("template_names", [&]() {
			for (auto decl : mod.template_declarations()) {
				name_test::test(decl, print, cprint);
			}
			for (auto decl : mod.template_definitions()) {
				name_test::test(decl, print, cprint);
			}
		});
	});
}
