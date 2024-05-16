/*
 * Copyright (c) 2021-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
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
#include <set>

bool
should_print(const clang::DeclContext *ctxt) {
	if (isa<TranslationUnitDecl>(ctxt))
		return true;
	else if (auto rd = dyn_cast<RecordDecl>(ctxt)) {
		if (rd->isAnonymousStructOrUnion() || rd->isInAnonymousNamespace() ||
			rd->getName() != "")
			return false;
	} else if (auto td = dyn_cast<TagDecl>(ctxt)) {
		if (td->getName() != "")
			return false;
	} else if (auto ns = dyn_cast<NamespaceDecl>(ctxt)) {
		if (ns->isAnonymousNamespace())
			return false;
	}
	return should_print(ctxt->getParent());
}

std::string &
replace_space(std::string &s) {
	auto cur = s.find_first_of(' ');
	while (cur != std::string::npos) {
		s[cur] = '_';
		cur = s.find_first_of(' ', cur);
	}
	return s;
}

void
write_globals(::Module &mod, CoqPrinter &print, ClangPrinter &cprint) {
	print.output() << "Module _'." << fmt::indent << fmt::line;
	std::set<std::string> notations;
	auto track = [&](std::string &s) {
		if (notations.find(s) != notations.end()) {
			llvm::errs() << "Warning: overlapping notation! '" << s << "'\n";
			return false;
		} else {
			notations.insert(s);
			return true;
		}
	};

	auto write_notations = [&](const clang::NamedDecl *def) {
		if (!def->getIdentifier() or !should_print(def->getDeclContext()))
			return;
		std::string s_notation;
		llvm::raw_string_ostream notation{s_notation};
		llvm::StringRef def_name = def->getName();

		// We prefix names with '::', but we could probably drop this, it doesn't really
		// add anything unless, at some point, we allow fuzzy matching such that `C` might
		// match `::NS::C`.
		notation << "::";
		def->getNameForDiagnostic(
			notation, PrintingPolicy(cprint.getContext().getLangOpts()), true);
		notation.flush();

		// we don't really have a way to escape "'", so do not emit notation that contains
		// that character.
		if (s_notation.find('\'') != std::string::npos)
			return;

		if (def_name == "__builtin_va_list" || def_name.startswith("__SV") ||
			def_name.startswith("__clang_sv"))
			return;
		if (const FieldDecl *fd = dyn_cast<FieldDecl>(def)) {
			track(s_notation);
			print.output() << "Notation \"'" << replace_space(s_notation)
						   << "'\" :=" << fmt::indent << fmt::nbsp;
			cprint.printField(fd, print);
			print.output() << " (in custom cppglobal at level 0)."
						   << fmt::outdent << fmt::line;
		} else if (const RecordDecl *rd = dyn_cast<RecordDecl>(def)) {
			if (!rd->isAnonymousStructOrUnion() &&
				rd->getNameAsString() != "") {
				print.output() << "Notation \"'" << replace_space(s_notation)
							   << "'\" :=" << fmt::indent << fmt::nbsp;
				track(s_notation);
				cprint.printTypeName(*rd, print);
				print.output() << "%bs (in custom cppglobal at level 0)."
							   << fmt::outdent << fmt::line;
			}

			std::string cls_name = s_notation;
			cls_name += "::";
			for (auto fd : rd->fields()) {
				if (fd->getName() != "") {
					s_notation.clear();
					notation << cls_name << fd->getName();
					track(s_notation);
					print.output()
						<< "Notation \"'" << replace_space(s_notation)
						<< "'\" :=" << fmt::nbsp << fmt::indent;
					cprint.printField(fd, print);
					print.output() << " (in custom cppglobal at level 0)."
								   << fmt::outdent << fmt::line;
				}
			}
		} else if (const EnumDecl *ed = dyn_cast<EnumDecl>(def)) {
			print.output() << "Notation \"'" << replace_space(s_notation)
						   << "'\" :=" << fmt::nbsp << fmt::indent;
			track(s_notation);

			cprint.printTypeName(ed, print, loc::of(ed));
			print.output()
				<< "%bs (only parsing, in custom cppglobal at level 0)."
				<< fmt::outdent << fmt::line;

		} else if (isa<FunctionDecl>(def)) {
			// todo(gmm): skipping due to function overloading
		} else if (auto ecd = dyn_cast<EnumConstantDecl>(def)) {
			notation << ecd->getName();
			print.output() << "Notation \"'" << replace_space(s_notation)
						   << "'\" :=" << fmt::indent;
			track(s_notation);

			cprint.printObjName(ecd, print, loc::of(ed));
			print.output()
				<< "%bs (only parsing, in custom cppglobal at level 0)."
				<< fmt::outdent << fmt::line;
		} else if (const TypedefDecl *td = dyn_cast<TypedefDecl>(def)) {
			if (td->isTemplated())
				return;

			print.output() << "Notation \"'" << replace_space(s_notation)
						   << "'\" :=" << fmt::nbsp << fmt::indent;
			track(s_notation);

			cprint.printQualType(td->getUnderlyingType(), print, loc::of(td));
			print.output() << " (only parsing, in custom cppglobal at level 0)."
						   << fmt::outdent << fmt::line;
		} else if (const auto *ta = dyn_cast<TypeAliasDecl>(def)) {
			if (ta->isTemplated())
				return;
			print.output() << "Notation \"'" << replace_space(s_notation)
						   << "'\" :=" << fmt::nbsp << fmt::indent;
			track(s_notation);

			cprint.printQualType(ta->getUnderlyingType(), print, loc::of(ta));
			print.output() << " (only parsing, in custom cppglobal at level 0)."
						   << fmt::outdent << fmt::line;
		} else if (const auto *vd = dyn_cast<VarDecl>(def)) {
			print.output() << "Notation \"'" << replace_space(s_notation)
						   << "'\" :=" << fmt::nbsp << fmt::indent;
			track(s_notation);
			cprint.printObjName(vd, print, loc::of(vd));
			print.output()
				<< "%bs (only parsing, in custom cppglobal at level 0)."
				<< fmt::outdent << fmt::line;
		} else {
			using namespace logging;
			log(Level::VERBOSE) << "unknown declaration type "
								<< def->getDeclKindName() << "\n";
		}
	};

	// todo(gmm): i would like to generate function names.
	for (auto def : mod.definitions())
		write_notations(def);
	for (auto def : mod.declarations())
		write_notations(def);

	print.output() << fmt::outdent << "End _'." << fmt::line;
	print.output() << "Export _'." << fmt::line << fmt::line;
}
