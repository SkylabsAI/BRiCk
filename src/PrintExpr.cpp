/*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "OpaqueNames.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/TargetInfo.h"
#include <bit>
#include <clang/Basic/Version.inc>

using namespace clang;
using namespace fmt;

enum Done : unsigned {
	NONE = 0,
	V = 1,
	T = 2,
	O = 4,
	VT = V | T,
	DT = 8,
};

fmt::Formatter&
ClangPrinter::printOverloadableOperator(clang::OverloadedOperatorKind oo,
										CoqPrinter& print, loc::loc loc) {
	if (trace(Trace::Expr))
		trace("printOverloadableOperator", loc);
	auto with_array = [&](StringRef name, bool array) -> auto& {
		guard::ctor _(print, name, false);
		return print.boolean(array);
	};
	switch (oo) {
	case OO_New:
		return with_array("OONew", false);
	case OO_Array_New:
		return with_array("OONew", true);
	case OO_Delete:
		return with_array("OODelete", false);
	case OO_Array_Delete:
		return with_array("OODelete", true);
	default:
		break;
	}
	switch (oo) {
#define OVERLOADED_OPERATOR(Name, Spelling, Token, Unary, Binary, MemberOnly)  \
	case OO_##Name:                                                            \
		return print.output() << "OO" << #Name;
#include "clang/Basic/OperatorKinds.def"
#undef OVERLOADED_OPERATOR
#undef OVERLOADED_OPERATOR_MULTI
	default:
		error_prefix(logging::fatal(), loc)
			<< "unknown overloadable operator " << oo << "\n";
		logging::die();
	}
}

void
printOptionalExpr(std::optional<const Expr*> expr, CoqPrinter& print,
				  ClangPrinter& cprint, OpaqueNames& li) {
	if (expr.has_value() && expr.value()) {
		print.some();
		cprint.printExpr(expr.value(), print, li);
		print.end_ctor();
	} else {
		print.none();
	}
}

bool
is_dependent(const Expr* expr) {
	return static_cast<bool>(expr->getDependence() &
							 ExprDependence::TypeValueInstantiation);
}

bool
is_static_member(ValueDecl* decl) {
	if (auto field = dyn_cast<FieldDecl>(decl)) {
		return not field->isCXXInstanceMember();
	} else if (auto meth = dyn_cast<CXXMethodDecl>(decl)) {
		return meth->isStatic();
	} else if (auto vd = dyn_cast<VarDecl>(decl)) {
		return true; // vd->isStaticLocal();
	} else {
		decl->dump();
		llvm::errs().flush();
		always_assert(false && "unsupported [is_static_member]");
		return false;
	}
}

// todo(gmm): this is duplicated!
bool
is_builtin(const Decl* d) {
	if (const FunctionDecl* fd = dyn_cast_or_null<const FunctionDecl>(d)) {
		if (Builtin::ID::NotBuiltin != fd->getBuiltinID()) {
			return true;
		}
	}
	return false;
}

fmt::Formatter&
ClangPrinter::printValueDeclExpr(const ValueDecl* decl, CoqPrinter& print,
								 OpaqueNames& on) {
	if (trace(Trace::Expr))
		trace("printValueDeclExpr", loc::of(decl));
	auto check_static_local = [](const ValueDecl* decl) {
		auto t = dyn_cast<VarDecl>(decl);
		return t && t->isStaticLocal();
	};
	auto t = on.find_anon(decl);
	if (t != -1) {
		print.ctor("Evar", false) << "(localname.anon " << t << ")";
	} else if (decl->getDeclContext()->isFunctionOrMethod() and
			   not(isa<FunctionDecl>(decl) or check_static_local(decl))) {
		print.ctor("Evar", false);
		if (auto pd = dyn_cast<ParmVarDecl>(decl)) {
			printParamName(pd, print);
		} else {
			printUnqualifiedName(*decl, print);
		}
	} else {
		print.ctor("Eglobal", false);
		printName(*decl, print);
	}
	print.output() << fmt::nbsp;
	printQualType(decl->getType(), print, loc::of(decl));
	return print.end_ctor();
}

fmt::Formatter&
ClangPrinter::printValueDeclExpr(const ValueDecl* decl, CoqPrinter& print) {
	OpaqueNames names;
	return printValueDeclExpr(decl, print, names);
}

/**
 * This class prints a dependent name (of Coq type [Mname]).
 */
struct PrintDependentName : public ConstStmtVisitor<PrintDependentName, void> {

	PrintDependentName(CoqPrinter& print_, ClangPrinter& cprint_)
		: print(print_), cprint(cprint_) {}

	void printDeclarationName(const DeclarationName& name) {
		/*
		TODO: This seems

		- A bit limited --- compare to/share code with structured::printFunctionName

		- A bit off --- `name.getAsString` does not account for `Ndtor` etc
		*/
		switch (name.getNameKind()) {
		case DeclarationName::NameKind::Identifier: {
			/*
			Example: A function name that couldn't be resolved due to an
			argument depending on a template parameter.
			*/

			auto atomic = [&]() -> fmt::Formatter& {
				{
					guard::ctor _(print, "Nfunction", false);
					print.output() << "nil" << fmt::nbsp;
					{
						guard::ctor _(print, "Nf", false);
						print.str(name.getAsString());
					}
					return print.output() << fmt::nbsp << "nil";
				}
			};

			atomic();
			break;
		}

		default:
			llvm::errs() << "printDeclarationName(" << name.getNameKind()
						 << ")";
			name.dump();
			print.output() << "(Nunsupported \"printDeclarationName("
						   << name.getNameKind() << ")\")";
		}
	}

	void Visit(const Expr* expr) {
		llvm::errs() << "printDependentName(" << expr->getStmtClassName()
					 << ")\n";
		expr->dump();
		ConstStmtVisitor<PrintDependentName, void>::Visit(expr);
	}

	void printNestedName(const DeclarationName& name,
						 const NestedNameSpecifierLoc nnl) {
		auto nn = nnl.getNestedNameSpecifier();
		if (not nn) {
			guard::ctor _(print, "Nglobal");
			printDeclarationName(name);
		} else if (nn->getKind() == NestedNameSpecifier::Global) {
			guard::ctor _(print, "Nglobal");
			printDeclarationName(name);
		} else {
			guard::ctor _(print, "Nscoped");
			cprint.printName(nn, print, loc::loc(nnl.getBeginLoc()));
			print.output() << fmt::nbsp;
			printDeclarationName(name);
		}
	}

	void VisitDependentScopeDeclRefExpr(const DependentScopeDeclRefExpr* expr) {
		if (expr->hasExplicitTemplateArgs()) {
			guard::ctor _(print, "Ninst");
			printNestedName(expr->getDeclName(), expr->getQualifierLoc());
			print.output() << fmt::nbsp;
			cprint.printTemplateArgumentList(expr->template_arguments(), print);
		} else {
			printNestedName(expr->getDeclName(), expr->getQualifierLoc());
		}
	}

	void VisitUnresolvedLookupExpr(const UnresolvedLookupExpr* expr) {
		printNestedName(expr->getName(), expr->getQualifierLoc());
	}

	void VisitUnresolvedMemberExpr(const UnresolvedMemberExpr* expr) {
		auto name = expr->getName();
		llvm::errs() << "printDeclarationName(" << expr->getName().getNameKind()
					 << ")";
		name.dump();

		print.output() << "(Nunsupported \"VisitnresolvedMemberExpr\")";
	}

	void VisitExpr(const Expr* expr) {
		llvm::errs() << "PrintDependentName(" << expr->getStmtClassName()
					 << ")\n";
		expr->dump();
		always_assert(false && "expression is no an overload expression");
	}

private:
	CoqPrinter& print;
	ClangPrinter& cprint;
};

/**
 * This class prints an expression (of Coq type [Expr] or [MExpr])
 */
class PrintExpr : public ConstStmtVisitor<PrintExpr, void> {
private:
	CoqPrinter& print;
	ClangPrinter& cprint;
	const ASTContext& ctxt;
	OpaqueNames& names;

	fmt::Formatter& printDeclType(const Expr* expr) {
		if (expr->isLValue()) {
			guard::ctor _(print, "Tref", false);
			cprint.printQualType(expr->getType(), print, loc::of(expr));
		} else if (expr->isXValue()) {
			guard::ctor _(print, "Trv_ref", false);
			cprint.printQualType(expr->getType(), print, loc::of(expr));
		} else {
			cprint.printQualType(expr->getType(), print, loc::of(expr));
		}
		return print.output();
	}

	fmt::Formatter& done(const Expr* expr, Done want = Done::T) {
		if (want == Done::DT) {
			printDeclType(expr);
		} else {
			if (want & Done::V) {
				print.output() << fmt::nbsp;
				cprint.printValCat(expr, print);
			}
			if (want & Done::T) {
				print.output() << fmt::nbsp;
				cprint.printQualType(expr->getType(), print, loc::of(expr));
			}
			if (want & Done::O) {
				print.output() << fmt::nbsp;
				cprint.printQualTypeOption(expr->getType(), print,
										   loc::of(expr));
			}
		}
		return print.end_ctor();
	}

public:
	PrintExpr(CoqPrinter& print, ClangPrinter& cprint, OpaqueNames& names)
		: print(print), cprint(cprint), ctxt(cprint.getContext()),
		  names(names) {}

	void VisitStmt(const Stmt* stmt) {
		logging::fatal() << "Error: while printing an expr, got a statement '"
						 << stmt->getStmtClassName() << " at "
						 << cprint.sourceRange(stmt->getSourceRange()) << "'\n";
		logging::die();
	}

	void unsupported_expr(const Expr* expr,
						  std::optional<StringRef> msg = std::nullopt,
						  bool well_known = false) {
		auto loc = loc::of(expr);
		if (!well_known || ClangPrinter::warn_well_known) {
			auto fullmsg = Twine("unsupported expression");
			if (msg) {
				fullmsg.concat(Twine(": "));
				fullmsg.concat(Twine(*msg));
			}
			cprint.error_prefix(logging::unsupported(), loc)
				<< "warning: " << fullmsg << "\n";
			cprint.debug_dump(loc);
		}
		print.ctor("Eunsupported");
		std::string coqmsg;
		llvm::raw_string_ostream os{coqmsg};
		os << loc::describe(loc, cprint.getContext());
		print.str(coqmsg);
		done(expr, Done::DT);
	}

	void VisitExpr(const Expr* expr) {
		unsupported_expr(expr);
	}

#define IGNORE(E)                                                              \
	void Visit##E(const E* expr) {                                             \
		unsupported_expr(expr, std::nullopt, /*well_known*/ true);             \
	}

	IGNORE(StmtExpr) // a GNU extension used in BHV

	// TODO: Discuss
	IGNORE(CXXRewrittenBinaryOperator)

	// These are template TODOs
	IGNORE(CXXUnresolvedConstructExpr)
	IGNORE(SizeOfPackExpr) // used in BHV

	void VisitDependentScopeDeclRefExpr(const DependentScopeDeclRefExpr* expr) {
		if (!print.templates())
			return unsupported_expr(expr);

		guard::ctor _(print, "Eunresolved_global");
		PrintDependentName{print, cprint}.Visit(expr);
	}

	void VisitUnresolvedLookupExpr(const UnresolvedLookupExpr* expr) {
		if (!print.templates())
			return unsupported_expr(expr);

		guard::ctor _(print, "Eunresolved_global");
		PrintDependentName{print, cprint}.Visit(expr);
	}

	void VisitRecoveryExpr(const RecoveryExpr* expr) {
		using namespace logging;
		unsupported() << "Error detected when typechecking C++ code at "
					  << cprint.sourceRange(expr->getSourceRange()) << "\n"
					  << "Try fixing earlier errors\n";
		print.ctor("Eunsupported");
		print.str(expr->getStmtClassName());
		done(expr, Done::VT);
	}

	void printBinaryOperator(const BinaryOperator* expr) {
		switch (expr->getOpcode()) {
#define CASE(k, s)                                                             \
	case BinaryOperatorKind::BO_##k:                                           \
		print.output() << s;                                                   \
		break;
			CASE(Add, "Badd")
			CASE(And, "Band")
			CASE(Cmp, "Bcmp")
			CASE(Div, "Bdiv")
			CASE(EQ, "Beq")
			CASE(GE, "Bge")
			CASE(GT, "Bgt")
			CASE(LE, "Ble")
			CASE(LT, "Blt")
			CASE(Mul, "Bmul")
			CASE(NE, "Bneq")
			CASE(Or, "Bor")
			CASE(Rem, "Bmod")
			CASE(Shl, "Bshl")
			CASE(Shr, "Bshr")
			CASE(Sub, "Bsub")
			CASE(Xor, "Bxor")
			CASE(PtrMemD, "Bdotp")
			CASE(PtrMemI, "Bdotip")
#undef CASE
		default:
			logging::unsupported()
				<< "defaulting binary operator"
				<< " (at " << cprint.sourceRange(expr->getSourceRange())
				<< ")\n";
			print.ctor("Bunsupported")
				<< "\"" << expr->getOpcodeStr() << "\"" << fmt::rparen;
			break;
		}
	}

	void VisitBinaryOperator(const BinaryOperator* expr) {
#define ACASE(k, v)                                                            \
	case BinaryOperatorKind::BO_##k##Assign:                                   \
		print.ctor("Eassign_op") << #v << fmt::nbsp;                           \
		break;
		[[maybe_unused]] auto dependent =
			print.templates() && expr->getType()->isDependentType();
		switch (expr->getOpcode()) {
		case BinaryOperatorKind::BO_Comma:
			print.ctor("Ecomma");
			cprint.printExpr(expr->getLHS(), print);
			print.output() << fmt::nbsp;
			cprint.printExpr(expr->getRHS(), print);
			// TODO: Can be overloaded
			always_assert(
				(dependent || expr->getRHS()->getType() == expr->getType()) &&
				"types must match");
			print.end_ctor(); // no type information
			return;
		case BinaryOperatorKind::BO_LAnd:
			print.ctor("Eseqand");
			cprint.printExpr(expr->getLHS(), print);
			print.output() << fmt::nbsp;
			cprint.printExpr(expr->getRHS(), print);
			// TODO: Can be overloaded
			always_assert(
				(dependent || expr->getType().getTypePtr()->isBooleanType()) &&
				"&& is a bool");
			print.end_ctor(); // no type information
			return;
		case BinaryOperatorKind::BO_LOr:
			print.ctor("Eseqor");
			cprint.printExpr(expr->getLHS(), print);
			print.output() << fmt::nbsp;
			cprint.printExpr(expr->getRHS(), print);
			// TODO: Can be overloaded
			always_assert(
				(dependent || expr->getType().getTypePtr()->isBooleanType()) &&
				"|| is a bool");
			print.end_ctor(); // no type information
			return;
		case BinaryOperatorKind::BO_Assign:
			print.ctor("Eassign");
			break;
			ACASE(Add, Badd)
			ACASE(And, Band)
			ACASE(Div, Bdiv)
			ACASE(Mul, Bmul)
			ACASE(Or, Bor)
			ACASE(Rem, Bmod)
			ACASE(Shl, Bshl)
			ACASE(Shr, Bshr)
			ACASE(Sub, Bsub)
			ACASE(Xor, Bxor)
		default:
			print.ctor("Ebinop");
			printBinaryOperator(expr);
			print.output() << fmt::nbsp;
			break;
		}
#undef ACASE
		cprint.printExpr(expr->getLHS(), print, names);
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getRHS(), print, names);
		done(expr, print.templates() ? Done::O : Done::T);
	}

	void printUnaryOperator(const UnaryOperator* expr) {
		switch (expr->getOpcode()) {
#define CASE(k, s)                                                             \
	case UnaryOperatorKind::UO_##k:                                            \
		print.output() << s;                                                   \
		break;
			CASE(Plus, "Uplus")
			CASE(Minus, "Uminus")
			CASE(Not, "Ubnot")
			CASE(LNot, "Unot")
			CASE(PostDec, "<PostDec>")
			CASE(PostInc, "<PostInc>")
			CASE(PreDec, "<PreDec>")
			CASE(PreInc, "<PreInc>")
#undef CASE
		default:
			logging::unsupported()
				<< "Error: unsupported unary operator"
				<< " (at " << cprint.sourceRange(expr->getSourceRange())
				<< ")\n";
			print.output() << "(Uunsupported \""
						   << UnaryOperator::getOpcodeStr(expr->getOpcode())
						   << "\")";
			break;
		}
	}

	void VisitUnaryOperator(const UnaryOperator* expr) {
		switch (expr->getOpcode()) {
		case UnaryOperatorKind::UO_AddrOf: {
			auto e = expr->getSubExpr();
			if (auto dre = dyn_cast<DeclRefExpr>(e)) {
				auto decl = dre->getDecl();
				if (not is_static_member(decl)) {
					guard::ctor _(print, "Eglobal_member");
					cprint.printName(decl, print, loc::of(expr));
					print.output() << fmt::nbsp;
					cprint.printQualType(decl->getType(), print, loc::of(expr));
					return;
				}
			}
			print.ctor("Eaddrof");
			cprint.printExpr(e, print, names);
			print.end_ctor(); // elide type
			return;
		}
		case UnaryOperatorKind::UO_Deref:
			print.ctor("Ederef");
			break;
		case UnaryOperatorKind::UO_PostInc:
			print.ctor("Epostinc");
			break;
		case UnaryOperatorKind::UO_PreInc:
			print.ctor("Epreinc");
			break;
		case UnaryOperatorKind::UO_PostDec:
			print.ctor("Epostdec");
			break;
		case UnaryOperatorKind::UO_PreDec:
			print.ctor("Epredec");
			break;
		default:
			print.ctor("Eunop");
			printUnaryOperator(expr);
			print.output() << fmt::nbsp;
		}
		cprint.printExpr(expr->getSubExpr(), print, names);
		done(expr, print.templates() ? Done::O : Done::T);
	}

	void VisitDeclRefExpr(const DeclRefExpr* expr) {
		auto d = expr->getDecl();
		if (!d) {
			cprint.error_prefix(logging::fatal(), loc::of(expr))
				<< "DeclRefExpr missing Decl\n";
			print.die();
		}
		if (ClangPrinter::debug && cprint.trace(Trace::Expr)) {
			auto& os = cprint.trace("VisitDeclRefExpr", loc::of(expr));
			auto loc = loc::of(d);
			if (loc::can_describe(loc))
				os << "Declaration: " << loc::describe(loc, cprint.getContext())
				   << "\n";
		}
		if (auto ecd = dyn_cast<EnumConstantDecl>(d)) {
			// References to `enum` constants are special because
			// they can be referenced both at the enumeration type
			// and (within the `enum` declaration) they can be
			// referenced at the underlying type. Here, we
			// unify these two so that the type of a reference to
			// an `enum` constant is *always* the `enum` type.
			// To match the type of the expression, we insert
			// an implicit integral cast.

			auto ed = dyn_cast<EnumDecl>(ecd->getDeclContext());
			if (expr->getType()->isEnumeralType()) {
				print.ctor("Eenum_const", false);
				cprint.printName(ed, print, loc::of(ecd));
				print.output() << fmt::nbsp;
				cprint.printUnqualifiedName(*ecd, print);
				print.end_ctor();
			} else {
				// TODO: is it possible to determine the `DeclContext` that
				// this expression occurs in? If so, then we could assert that
				// this is in the scope of the enumeration.
				print.ctor("Eenum_const_at", false);
				cprint.printName(ed, print, loc::of(ecd));
				print.output() << fmt::nbsp;
				cprint.printUnqualifiedName(*ecd, print);
				print.output() << fmt::nbsp;
				done(expr);
			}
		} else if (auto param = dyn_cast<NonTypeTemplateParmDecl>(d)) {
			if (print.templates()) {
				// TODO: Add some tests
				guard::ctor _(print, "Eparam");
				cprint.printUnqualifiedName(*param, print);
			} else {
				unsupported_expr(expr, std::nullopt,
								 /*well_known*/ true);
			}
		} else {
			cprint.printValueDeclExpr(d, print, names);
		}
	}

	void VisitCallExpr(const CallExpr* expr) {
		auto callee = expr->getCallee();
		if (is_dependent(expr)) {
			/*
			Either the function or an argument is dependent.
			*/
			guard::ctor ctor(print, "Eunresolved_call");
			PrintDependentName{print, cprint}.Visit(callee);
			print.output() << fmt::nbsp;
			print.list(expr->arguments(),
					   [&](auto i) { cprint.printExpr(i, print, names); });
		} else if (auto pd = dyn_cast<CXXPseudoDestructorExpr>(callee)) {
			// in the clang AST, pseudo destructors are represented as calls
			// but in the BRiCk AST, they are their own construct.
			always_assert(expr->arguments().empty());
			print.ctor("Epseudo_destructor")
				<< fmt::BOOL(pd->isArrow()) << fmt::nbsp;
			cprint.printQualType(pd->getDestroyedType(), print, loc::of(pd));
			print.output() << fmt::nbsp;
			cprint.printExpr(pd->getBase(), print, names);
			print.end_ctor();
		} else {
			print.ctor("Ecall");
			cprint.printExpr(expr->getCallee(), print, names);
			print.output() << fmt::line;
			print.list(expr->arguments(),
					   [&](auto i) { cprint.printExpr(i, print, names); });
			done(expr, Done::NONE);
		}
	}

	void VisitCXXOperatorCallExpr(const CXXOperatorCallExpr* expr) {
		// TODO operator calls sometimes have stricter order of evaluation
		// than regular function calls. Because our semantics overapproximates
		// the possible behaviors, it is sound for us to directly desugar them.
		auto callee = expr->getCalleeDecl();
		// some operator calls are actually method calls.
		// because we (and C++) distinguish between member calls
		// and function calls, we need to desugar this to a method
		// if the called function is a method.
		if (auto method = dyn_cast<CXXMethodDecl>(callee)) {
			always_assert(!method->isStatic() &&
						  "operator overloads can not be static");
			print.ctor("Eoperator_member_call");
			cprint.printOverloadableOperator(expr->getOperator(), print,
											 loc::of(expr))
				<< fmt::nbsp;

			cprint.printName(*method, print);
			print.output() << fmt::nbsp
						   << (method->isVirtual() ? "Virtual" : "Direct")
						   << fmt::nbsp;
			cprint.printQualType(method->getType(), print, loc::of(method));
			print.output() << fmt::nbsp;

			cprint.printExpr(expr->getArg(0), print, names);

			print.output() << fmt::nbsp;
			// note skip the first parameter because it is the object.
			print.list_range(
				expr->arg_begin() + 1, expr->arg_end(),
				[&](auto i) { cprint.printExpr(i, print, names); });

		} else if (auto function = dyn_cast<FunctionDecl>(callee)) {
			print.ctor("Eoperator_call");
			cprint.printOverloadableOperator(expr->getOperator(), print,
											 loc::of(expr))
				<< fmt::nbsp;

			cprint.printName(*function, print);
			print.output() << fmt::nbsp;
			cprint.printQualType(function->getType(), print, loc::of(function));
			print.output() << fmt::nbsp;
			print.list(expr->arguments(),
					   [&](auto i) { cprint.printExpr(i, print, names); });
		} else {
			logging::unsupported() << "unsupported operator call";
			logging::die();
		}

		done(expr, Done::NONE);
	}

	void printCast(const CastExpr* ce) {
		auto with_type = [&](const char* c) {
			guard::ctor _(print, c, false);
			printDeclType(ce);
		};
		auto without_type = [&](const char* c) { print.output() << c; };

		switch (ce->getCastKind()) {
#define CASE_NO_TYPE(a, b)                                                     \
	case CastKind::CK_##a:                                                     \
		without_type(#b);                                                      \
		break;
#define CASE_WITH_TYPE(a, b)                                                   \
	case CastKind::CK_##a:                                                     \
		with_type(#b);                                                         \
		break;
			CASE_WITH_TYPE(BitCast, Cbitcast)
			CASE_WITH_TYPE(LValueBitCast, Clvaluebitcast)
			CASE_NO_TYPE(LValueToRValue, Cl2r)
			CASE_WITH_TYPE(NoOp, Cnoop)
			CASE_NO_TYPE(ArrayToPointerDecay, Carray2ptr)
			CASE_NO_TYPE(FunctionToPointerDecay, Cfun2ptr)
			CASE_WITH_TYPE(IntegralToPointer, Cint2ptr)
			CASE_WITH_TYPE(PointerToIntegral, Cptr2int)

			CASE_NO_TYPE(PointerToBoolean, Cptr2bool)
			CASE_WITH_TYPE(IntegralCast, Cintegral)
			CASE_NO_TYPE(IntegralToBoolean, Cint2bool)

			CASE_WITH_TYPE(NullToPointer, Cnull2ptr)
			CASE_WITH_TYPE(NullToMemberPointer, Cnull2memberptr)

			CASE_WITH_TYPE(BuiltinFnToFnPtr, Cbuiltin2fun)

			CASE_WITH_TYPE(ConstructorConversion, Cctor)
			CASE_NO_TYPE(UserDefinedConversion, Cuser)

			CASE_NO_TYPE(ToVoid, C2void)

			// floating point casts
			CASE_WITH_TYPE(FloatingToIntegral, Cfloat2int)

			CASE_WITH_TYPE(Dependent, Cdependent)
#undef CASE_NO_TYPE
#undef CASE_WITH_TYPE

		case CastKind::CK_DerivedToBase:
		case CastKind::CK_UncheckedDerivedToBase: {
			print.ctor("Cderived2base");
			// note that [path] does *not* include the type of the argument
			print.list(ce->path(), [&](auto i) {
				auto t = i->getType().getTypePtrOrNull();
				always_assert(t && "Cderived2base without type");
				cprint.printType(*t, print, loc::of(ce));
			});
			done(ce, Done::DT);
			break;
		}
		case CastKind::CK_BaseToDerived:
			print.ctor("Cbase2derived");
			// note that [path] does *not* include the type of the argument
			print.list(ce->path(), [&](auto i) {
				auto t = i->getType().getTypePtrOrNull();
				always_assert(t && "Cbase2derived without type");
				cprint.printType(*t, print, loc::of(ce));
			});
			done(ce, Done::DT);
			break;
		default:
			logging::unsupported()
				<< "unsupported cast kind \"" << ce->getCastKindName() << "\""
				<< " (at " << cprint.sourceRange(ce->getSourceRange()) << ")\n";
			print.output() << "Cunsupported";
		}
	}

	void VisitExplicitCastExpr(const ExplicitCastExpr* expr) {
		if (isa<CStyleCastExpr>(expr)) {
			print.ctor("Ecstyle_cast");
		} else if (auto nc = dyn_cast<CXXNamedCastExpr>(expr)) {
			print.ctor(llvm::Twine("E") + nc->getCastName());
		} else if (isa<CXXFunctionalCastExpr>(expr)) {
			print.ctor("Efunctional_cast");
		} else {
			return unsupported_expr(expr, std::nullopt, false);
		}

		printCast(expr);
		print.output() << fmt::nbsp;
		cprint.printQualType(expr->getTypeAsWritten(), print, loc::of(expr));
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getSubExpr(), print, names);
		print.end_ctor();
	}

	void VisitImplicitCastExpr(const ImplicitCastExpr* expr) {
		// todo(gmm): this is a complete hack because there is no way that i know of
		// to get the type of a builtin. what this does is get the type of the expression
		// that contains the builtin.
		if (expr->getCastKind() == CastKind::CK_BuiltinFnToFnPtr) {
			auto ref = dyn_cast<DeclRefExpr>(expr->getSubExpr());
			always_assert(ref && "builtin function to function pointer must be "
								 "applied to a literal variable");
			always_assert(is_builtin(ref->getDecl()));
			print.ctor("Ebuiltin", false);
			// assume that this is a builtin
			cprint.printName(ref->getDecl(), print, loc::of(ref));
			print.output() << fmt::nbsp;
			auto type = expr->getType();
			always_assert(type->isPointerType() &&
						  "builtin to pointer is not a pointer");
			cprint.printQualType(type.getTypePtr()->getPointeeType(), print,
								 loc::of(expr));
			print.end_ctor();
			return;
		}

		guard::ctor _(print, "Ecast");
		printCast(expr);
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getSubExpr(), print, names);
	}

	void VisitCastExpr(const CastExpr* expr) {
		always_assert(false && "Cast expression should be unreachable");
	}

	void VisitIntegerLiteral(const IntegerLiteral* lit) {
		print.ctor("Eint", false);
		SmallString<32> s;
		if (lit->getType()->isSignedIntegerOrEnumerationType()) {
			lit->getValue().toStringSigned(s);
		} else {
			lit->getValue().toStringUnsigned(s);
		}
		print.output() << s << "%Z";
		done(lit);
	}

	void VisitCharacterLiteral(const CharacterLiteral* lit) {
		print.ctor("Echar", false) << lit->getValue() << "%N";
		done(lit);
	}

	static void print_string_type(const Expr* expr, CoqPrinter& print,
								  ClangPrinter& cprint) {
		if (auto at = dyn_cast<ArrayType>(expr->getType().getTypePtr())) {
			print.output() << fmt::nbsp;
			cprint.printType(at->getElementType().getTypePtr(), print,
							 loc::of(expr));
		} else {
			always_assert(false && "string literal does not have array type");
		}
	}

	void VisitStringLiteral(const StringLiteral* lit) {
		print.ctor("Estring", false);
		// We get the string literal in bytes, but we need to encode it
		// as unsigned characters (not necessarily `char`) using the
		// internal character representation of BRiCk.
		auto bytes = lit->getBytes();
		const unsigned width = lit->getCharByteWidth();
		print.begin_list();
#if 18 <= CLANG_VERSION_MAJOR
		namespace endianNS = llvm;
#else
		namespace endianNS = llvm::support;
#endif
		for (unsigned i = 0, len = lit->getByteLength(); i < len;) {
			unsigned long long byte = 0;
			// TODO confirm that this is correct
			if (endianNS::endianness::native == endianNS::endianness::big) {
				for (unsigned j = 0; j < width; ++j) {
					byte = (byte << 8) | static_cast<unsigned char>(bytes[i++]);
				}
			} else {
				for (unsigned j = 0; j < width; ++j) {
					byte = (byte << 8) |
						   static_cast<unsigned char>(bytes[i + width - j - 1]);
				}
				i += width;
			}
			print.output() << byte << "%N";
			print.cons();
		}
		print.end_list();
		// NOTE: the trailing `\0` is added by the semantics
		print_string_type(lit, print, cprint);
		print.end_ctor();
	}

	void VisitPredefinedExpr(const PredefinedExpr* expr) {
		// [PredefinedExpr] constructs a [string] which is always ascii
		print.ctor("Estring");
		print.ctor("BS.string_to_bytes");
		print.str(expr->getFunctionName()->getString());
		print.end_ctor();
		print_string_type(expr, print, cprint);
		print.end_ctor();
	}

	void VisitCXXBoolLiteralExpr(const CXXBoolLiteralExpr* lit) {
		if (lit->getValue()) {
			print.output() << "(Ebool true)";
		} else {
			print.output() << "(Ebool false)";
		}
	}

	void VisitFloatingLiteral(const FloatingLiteral* lit) {
		print.ctor("Eunsupported") << fmt::nbsp << "\"float: ";
		lit->getValue().print(print.output().nobreak());
		print.output() << "\"";
		done(lit, Done::VT);
	}

	void VisitMemberExpr(const MemberExpr* expr) {
		auto member = expr->getMemberDecl();

		print.ctor("Emember");
		print.boolean(expr->isArrow()) << fmt::nbsp;

		auto base = expr->getBase();
		cprint.printExpr(base, print, names);
		print.output() << fmt::nbsp;
		if (auto fd = dyn_cast<FieldDecl>(member)) {
			//print.str(expr->getMemberDecl()->getNameAsString());
			print.output() << "(inl ";
			cprint.printFieldName(*fd, print, loc::of(expr));
			print.output() << ")" << fmt::nbsp;
			print.boolean(fd->isMutable());
		} else if (auto vd = dyn_cast<VarDecl>(member)) {
			always_assert(vd->isStaticDataMember() &&
						  "variable referenced through member must be "
						  "a static data "
						  "member");
			print.output() << "(inr ";
			cprint.printName(*vd, print);
			print.output() << ")" << fmt::nbsp;
			print.boolean(false);
		} else if (auto md = dyn_cast<CXXMethodDecl>(member)) {
			print.output() << "(inr ";
			cprint.printName(*md, print);
			print.output() << ")" << fmt::nbsp;
			print.boolean(false);
		} else {
			logging::fatal() << "Unknown member in MemberExpr\n";
			logging::die();
		}
		print.output() << fmt::nbsp;

		// The type of the expression is determined by the type of the object,
		// the type of the member, and the mutability of the member.
		// The only piece of information that we are missing is the mutability
		// of the member.
		// We can compute the type of the full expression by
		// 1/ if the field type is reference, or rv_reference, that is type
		// 2/ otherwise, taking the qualifiers of the object, remove [const]
		//    if the field is [mutable], and then use the type of the field.
		cprint.printQualType(member->getType(), print, loc::of(member));
		print.end_ctor();
	}

	void
	VisitCXXDependentScopeMemberExpr(const CXXDependentScopeMemberExpr* expr) {
		print.ctor("Eunresolved_member");
		print.boolean(expr->isArrow()) << fmt::nbsp;
		cprint.printExpr(expr->getBase(), print, names);
		print.output() << fmt::nbsp;
		print.str(expr->getMember().getAsString());
		print.end_ctor();
	}

	void VisitArraySubscriptExpr(const ArraySubscriptExpr* expr) {
		// Array-to-pointer casts obscure value category inference because
		// the resulting pointer is a prvalue regardless of the value category
		// of the array. To make the typing rules composable, we drop this
		// cast and generalize the semantics of subscript to directly support
		// array types.
		auto under_cast = [](const Expr* expr) {
			if (auto ce = dyn_cast<ImplicitCastExpr>(expr)) {
				if (ce->getCastKind() == CastKind::CK_ArrayToPointerDecay)
					return ce->getSubExpr();
			}
			return expr;
		};

		print.ctor("Esubscript");
		cprint.printExpr(under_cast(expr->getLHS()), print, names);
		print.output() << fmt::nbsp;
		cprint.printExpr(under_cast(expr->getRHS()), print, names);
		done(expr, print.templates() ? Done::O : Done::T);
	}

	void VisitCXXConstructExpr(const CXXConstructExpr* expr) {
		print.ctor("Econstructor");
		// print.output() << expr->isElidable() << fmt::nbsp;
		cprint.printName(expr->getConstructor(), print, loc::of(expr));
		print.output() << fmt::nbsp;
		print.list(expr->arguments(),
				   [&](auto i) { cprint.printExpr(i, print, names); });
		//print.output() << fmt::nbsp << expr->isElidable();
		done(expr);
	}

	void VisitCXXInheritedCtorInitExpr(const CXXInheritedCtorInitExpr* expr) {
		print.ctor("Econstructor");
		// print.output() << expr->isElidable() << fmt::nbsp;
		auto ctor = expr->getConstructor();
		cprint.printName(ctor, print, loc::of(expr));
		print.output() << fmt::nbsp;
		// NOTE clang does not include the arguments to the constructor here
		// they are forwarded from the function itself; however, with the
		// data that we have, we can't get to the actual function.
		// A good solution would be to store this information in the [OpaqueNames]
		// object, but for now, we can get away with printing the variable references
		// directly.
		auto idx = 0;
		print.list(ctor->parameters(), [&](auto i) {
			print.ctor("Evar", false);
			print.output() << "(localname.anon " << idx << ")";
			print.output() << fmt::nbsp;
			cprint.printQualType(i->getType(), print, loc::of(i));
			print.end_ctor();
			++idx;
		});
		//print.output() << fmt::nbsp << expr->isElidable();
		done(expr);
	}

	void VisitCXXMemberCallExpr(const CXXMemberCallExpr* expr) {
		print.ctor("Emember_call");
		auto callee = expr->getCallee()->IgnoreParens();
		auto method = expr->getMethodDecl();
		if (auto me = dyn_cast<MemberExpr>(callee)) {
			print.output() << fmt::BOOL(me->isArrow()) << fmt::nbsp;

			print.ctor("inl") << fmt::lparen;
			cprint.printName(method, print, loc::of(expr));
			print.output() << "," << fmt::nbsp;
			if (method->isVirtual() &&
				me->performsVirtualDispatch(ctxt.getLangOpts())) {
				print.output() << "Virtual";
			} else {
				print.output() << "Direct";
			}
			print.output() << "," << fmt::nbsp;

			if (const CXXMethodDecl* const md =
					dyn_cast<CXXMethodDecl>(me->getMemberDecl())) {
				cprint.printQualType(md->getType(), print, loc::of(md));
			} else {
				always_assert(false &&
							  "MemberDecl in MemberCall must be a MethodDecl");
			}
			print.output() << fmt::rparen;
			print.end_ctor();

			print.output() << fmt::nbsp;
			cprint.printExpr(expr->getImplicitObjectArgument(), print, names);
		} else if (auto bo = dyn_cast<BinaryOperator>(callee)) {
			always_assert(bo->getOpcode() == BinaryOperatorKind::BO_PtrMemD ||
						  bo->getOpcode() == BinaryOperatorKind::BO_PtrMemI);
			print.output() << fmt::BOOL(bo->getOpcode() ==
										BinaryOperatorKind::BO_PtrMemI)
						   << fmt::nbsp;

			print.ctor("inr");
			cprint.printExpr(bo->getRHS(), print, names);
			print.end_ctor() << fmt::nbsp;

			cprint.printExpr(expr->getImplicitObjectArgument(), print, names);
		} else {
			always_assert(false && "no method and not a binary operator");
		}
		print.output() << fmt::nbsp;
		print.list(expr->arguments(),
				   [&](auto i) { cprint.printExpr(i, print, names); });
#if 0
	print.output() << fmt::nbsp << fmt::lparen;
	for (auto i : expr->arguments()) {
		cprint.printExpr(i, print, names);
		print.cons();
	}
	print.end_list();
#endif
		done(expr, Done::NONE);
	}

	void VisitCXXDefaultArgExpr(const CXXDefaultArgExpr* expr) {
		print.ctor("Eimplicit");
		cprint.printExpr(expr->getExpr(), print, names);
		print.end_ctor();
	}

	void VisitConditionalOperator(const ConditionalOperator* expr) {
		print.ctor("Eif");
		cprint.printExpr(expr->getCond(), print, names);
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getTrueExpr(), print, names);
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getFalseExpr(), print, names);
		done(expr, Done::DT);
	}

	void VisitBinaryConditionalOperator(const BinaryConditionalOperator* expr) {
		print.ctor("Eif2");
		auto index = names.fresh(expr->getOpaqueValue());
		print.output() << index << fmt::nbsp;
		cprint.printExpr(expr->getCommon(), print, names);
		names.inc_index_count();
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getCond(), print, names);
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getTrueExpr(), print, names);
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getFalseExpr(), print, names);
		names.dec_index_count();
		done(expr, Done::DT);
	}

	void VisitConstantExpr(const ConstantExpr* expr) {
		this->Visit(expr->getSubExpr());
	}

	void VisitParenExpr(const ParenExpr* e) {
		this->Visit(e->getSubExpr());
	}

	void VisitParenListExpr(const ParenListExpr* expr) {
		if (!print.templates()) {
			// This node type is purely syntactic.
			// When the type is known, the expression is represented
			// as [CXXConstructorExpr] or not represented at all, e.g.
			// in <<T x(1);>>.
			return unsupported_expr(expr);
		}
		print.ctor("Eunresolved_parenlist");

		cprint.printQualTypeOption(expr->getType(), print, loc::of(expr));
		print.output() << fmt::nbsp;

		// `print.list` unavailable because there's no constant
		// version of `ParenListExpr::exprs`.
		// TODO: Define and use iterator over integer ranges.

		auto n = expr->getNumExprs();
		if (n == 0)
			print.output() << "nil";
		else {
			print.begin_list();
			for (unsigned i = 0; i < n; i++) {
				cprint.printExpr(expr->getExpr(i), print, names);
				print.cons();
			}
			print.end_list();
		}
		print.end_ctor();
	}

	void VisitInitListExpr(const InitListExpr* expr) {
		if (expr->isTransparent()) {
			// "transparent" intializer lists are no-ops in the semantics
			// and are retained in the clang AST only for printing purposes.
			always_assert(expr->inits().size() == 1);
			cprint.printExpr(expr->getInit(0), print, names);
		} else {
			print.ctor("Einitlist");

			print.list(expr->inits(), [&](auto i) {
				cprint.printExpr(i, print, names);
			}) << fmt::nbsp;

			if (expr->getArrayFiller()) {
				print.some();
				cprint.printExpr(expr->getArrayFiller(), print, names);
				print.end_ctor();
			} else {
				print.none();
			}

			done(expr);
		}
	}

	void VisitCXXThisExpr(const CXXThisExpr* expr) {
		print.ctor("Ethis", false);
		done(expr);
	}

	void VisitCXXNullPtrLiteralExpr(const CXXNullPtrLiteralExpr* expr) {
		// <<nullptr>> has a special type
		print.output() << "Enull" << fmt::nbsp;
	}

	void VisitUnaryExprOrTypeTraitExpr(const UnaryExprOrTypeTraitExpr* expr) {
		auto do_arg = [&]() {
			if (expr->isArgumentType()) {
				print.ctor("inl", false);
				cprint.printQualType(expr->getArgumentType(), print,
									 loc::of(expr));
				print.output() << fmt::rparen;
			} else if (expr->getArgumentExpr()) {
				print.ctor("inr", false);
				cprint.printExpr(expr->getArgumentExpr(), print, names);
				print.output() << fmt::rparen;
			} else {
				always_assert(false);
				//fatal("argument to sizeof/alignof is not a type or an expression.");
			}
		};

		if (expr->getKind() == UnaryExprOrTypeTrait::UETT_AlignOf) {
			print.ctor("Ealignof", false);
			do_arg();
			done(expr);
		} else if (expr->getKind() == UnaryExprOrTypeTrait::UETT_SizeOf) {
			print.ctor("Esizeof", false);
			do_arg();
			done(expr);
		} else {
			using namespace logging;
			fatal() << "Error: unsupported expression "
					   "`UnaryExprOrTypeTraitExpr` at "
					<< expr->getSourceRange().printToString(
						   ctxt.getSourceManager())
					<< "\n";
			die();
		}
	}

	void VisitOffsetOfExpr(const OffsetOfExpr* expr) {
		auto unsupported = [&](const std::string what) {
			unsupported_expr(expr, what);
		};
		if (expr->getNumComponents() != 1)
			return unsupported(
				"offsetof with no components, or multiple components");

		auto comm = expr->getComponent(0);
		switch (comm.getKind()) {
		case OffsetOfNode::Kind::Field: {
			print.ctor("Eoffsetof");
			auto field = comm.getField();
			auto parent = field ? field->getParent() : nullptr;
			auto ty = parent ? parent->getTypeForDecl() : nullptr;
			always_assert(ty && "offsetof without type");

			cprint.printType(*ty, print, loc::of(expr)) << fmt::nbsp;
			print.str(comm.getField()->getName()) << fmt::nbsp;
			done(expr);
			return;
		}
		default:
			return unsupported(
				"offsetof only supported on fields and base classes");
		}
	}

	void VisitSubstNonTypeTemplateParmExpr(
		const SubstNonTypeTemplateParmExpr* expr) {
		this->Visit(expr->getReplacement());
	}

	void VisitCXXNewExpr(const CXXNewExpr* expr) {
		auto new_fn = expr->getOperatorNew();
		if (not new_fn) {
			logging::fatal() << "missing operator [new]\n";
			logging::die();
		}

		print.ctor("Enew");

		print.begin_tuple();
		cprint.printName(*new_fn, print);
		print.next_tuple();
		cprint.printQualType(new_fn->getType(), print, loc::of(new_fn));
		print.end_tuple() << fmt::nbsp;

		print.list(expr->placement_arguments(), [&](auto arg) {
			cprint.printExpr(arg, print, names);
		}) << fmt::nbsp;

		if (new_fn->isReservedGlobalPlacementOperator()) {
			always_assert(expr->getNumPlacementArgs() == 1 &&
						  "placement new gets a single argument");
			always_assert(!expr->passAlignment() &&
						  "alignment is not passed to placement new");
			print.output() << "new_form.NonAllocating" << fmt::nbsp;
		} else {
			print.ctor("new_form.Allocating")
				<< fmt::BOOL(expr->passAlignment()) << fmt::nbsp;
			print.end_ctor() << fmt::nbsp;
		}

		cprint.printQualType(expr->getAllocatedType(), print, loc::of(expr));

		print.output() << fmt::nbsp;

		// NOTE: the clang documentation says that this can return
		// None even if it is an array new, but I have not found a
		// way to trigger that.
		always_assert(expr->isArray() == (bool)expr->getArraySize());
		printOptionalExpr(expr->getArraySize(), print, cprint, names);

		print.output() << fmt::nbsp;

		printOptionalExpr(expr->getInitializer(), print, cprint, names);

		print.end_ctor();
	}

	void VisitCXXDeleteExpr(const CXXDeleteExpr* expr) {
		print.ctor("Edelete");
		print.output() << fmt::BOOL(expr->isArrayForm()) << fmt::nbsp;

		if (auto op = expr->getOperatorDelete()) {
			if (op->isDestroyingOperatorDelete()) {
				logging::fatal() << "destroying delete is not supported\n";
				logging::die();
			}
			print.begin_tuple();
			cprint.printName(*op, print);
			print.next_tuple();
			cprint.printQualType(op->getType(), print, loc::of(op));
			print.end_tuple();
		} else {
			logging::fatal() << "missing [delete] operator\n";
			logging::die();
		}
		print.output() << fmt::nbsp;

		cprint.printExpr(expr->getArgument(), print, names);

		print.output() << fmt::nbsp;

		cprint.printQualType(expr->getDestroyedType(), print, loc::of(expr));

		// no need to print the type information on [delete]
		print.end_ctor();
	}

	void VisitExprWithCleanups(const ExprWithCleanups* expr) {
		// NOTE candidate for removal
		// our semantics cleans everything, so we don't need to
		// mark this explicitly.
		print.ctor("Eandclean");
		if (ClangPrinter::debug && cprint.trace(Trace::Expr)) {
			auto& os = llvm::errs();
			os << "and_clean objects: " << expr->getNumObjects() << "\n";
			for (auto i : expr->getObjects()) {
				os << i.getOpaqueValue() << "\n";
			}
		}
		cprint.printExpr(expr->getSubExpr(), print, names);
		print.end_ctor();
	}

	void VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr* expr) {
		if (expr->getExtendingDecl() != nullptr) {
			using namespace logging;
			fatal() << "Error: binding a reference to a temporary is not "
					   "(yet?) supported "
					   "(scope extrusion)"
					<< expr->getSourceRange().printToString(
						   ctxt.getSourceManager())
					<< "\n";
			die();
		}

		print.ctor("Ematerialize_temp");
		cprint.printExpr(expr->getSubExpr(), print, names);
		done(expr, Done::V);
	}

	void VisitCXXBindTemporaryExpr(const CXXBindTemporaryExpr* expr) {
		// According to [clang docs](https://clang.llvm.org/doxygen/classclang_1_1CXXBindTemporaryExpr.html),
		// a CXXBindTemporary node "represents binding an expression to a temporary.
		// This ensures the destructor is called for the temporary.
		// It should only be needed for non-POD, non-trivially destructable class types."
		// We can omit these nodes because in our semantics, objects are *always* deleted with
		// destructors, even if the destructor is trivial. Thus, our semantics
		// essentially implicitly has a [BindTemporary] node around all automatic
		// storage duration aggregates.

		cprint.printExpr(expr->getSubExpr(), print, names);
	}

	void VisitOpaqueValueExpr(const OpaqueValueExpr* expr) {
		print.ctor("Eopaque_ref") << names.find(expr);
		done(expr, Done::DT);
	}

	void VisitAtomicExpr(const clang::AtomicExpr* expr) {
		print.ctor("Eatomic");

		switch (expr->getOp()) {
#define BUILTIN(ID, TYPE, ATTRS)
#define ATOMIC_BUILTIN(ID, TYPE, ATTRS)                                        \
	case clang::AtomicExpr::AO##ID:                                            \
		print.output() << "AO" #ID << fmt::nbsp;                               \
		break;
#include "clang/Basic/Builtins.def"
#undef BUILTIN
#undef ATOMIC_BUILTIN
		}

		print.begin_list();
		for (unsigned i = 0; i < expr->getNumSubExprs(); ++i) {
			cprint.printExpr(expr->getSubExprs()[i], print, names);
			print.cons();
		}
		print.end_list();

		done(expr);
	}

	void VisitCXXDefaultInitExpr(const CXXDefaultInitExpr* expr) {
		print.ctor("Edefault_init_expr");
		cprint.printExpr(expr->getExpr(), print, names);
		print.end_ctor();
	}

	void VisitVAArgExpr(const VAArgExpr* expr) {
		print.ctor("Eva_arg");
		cprint.printExpr(expr->getSubExpr(), print, names);
		done(expr);
	}

	void VisitLambdaExpr(const LambdaExpr* expr) {
		print.ctor("Eunsupported");
		print.str("lambda");
		done(expr, Done::VT);
	}

	void VisitImplicitValueInitExpr(const ImplicitValueInitExpr* expr) {
		print.ctor("Eimplicit_init");
		done(expr);
	}

	void VisitCXXPseudoDestructorExpr(const CXXPseudoDestructorExpr* expr) {
		print.ctor("Epseudo_destructor");
		cprint.printQualType(expr->getDestroyedType(), print, loc::of(expr));
		print.output() << fmt::nbsp;
		cprint.printExpr(expr->getBase(), print, names);
		print.end_ctor();
	}

	void VisitCXXNoexceptExpr(const CXXNoexceptExpr* expr) {
		// note: i should record the fact that this is a noexcept expression
		print.ctor("Ebool");
		print.boolean(expr->getValue());
		print.end_ctor();
	}

	void VisitTypeTraitExpr(const TypeTraitExpr* expr) {
		// note: i should record the fact that this is a noexcept expression
		print.ctor("Ebool");
		print.boolean(expr->getValue());
		print.end_ctor();
	}

	void VisitCXXScalarValueInitExpr(const CXXScalarValueInitExpr* expr) {
		print.ctor("Eimplicit_init");
		cprint.printQualType(expr->getType(), print, loc::of(expr));
		print.end_ctor();
	}

	void VisitArrayInitLoopExpr(const ArrayInitLoopExpr* expr) {
		print.ctor("Earrayloop_init");

		auto index = names.fresh(expr->getCommonExpr());
		print.output() << index << fmt::nbsp;

		// this is the source array which we are initializing
		auto src = expr->getCommonExpr()->getSourceExpr();
		cprint.printExpr(src, print, names);

		// this is the expression that is evaluated
		names.inc_index_count();
		print.output() << names.index_count() << fmt::nbsp
					   << expr->getArraySize() << fmt::nbsp;
		cprint.printExpr(expr->getSubExpr(), print, names);
		names.dec_index_count();
		names.free(
			expr->getCommonExpr()); // index goes out of scope at this point

		done(expr);
	}

	void VisitArrayInitIndexExpr(const ArrayInitIndexExpr* expr) {
		print.ctor("Earrayloop_index") << names.index_count() << fmt::nbsp;
		done(expr);
	}
};

fmt::Formatter&
ClangPrinter::printExpr(const clang::Expr* expr, CoqPrinter& print,
						OpaqueNames& li) {
	if (trace(Trace::Expr))
		trace("printExpr", loc::of(expr));

	auto depth = print.output().get_depth();
	PrintExpr{print, *this, li}.Visit(expr);
	if (depth != print.output().get_depth()) {
		using namespace logging;
		fatal() << "Error: BUG indentation bug in during: "
				<< expr->getStmtClassName() << " start = " << depth
				<< ", end = " << print.output().get_depth() << "\n";
		always_assert(false);
	}
	return print.output();
}

fmt::Formatter&
ClangPrinter::printExpr(const clang::Expr* expr, CoqPrinter& print) {
	OpaqueNames names;
	return printExpr(expr, print, names);
}
