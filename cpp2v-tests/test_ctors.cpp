struct D {};
struct C : public D { int x; };

int testC() {
  C c;
  c = C();
  C d;
  c = d;
  C e(c);
  C f{C()};
  return c.x;
}

struct X;
int foo(X);


#if 0
| `-CXXMethodDecl 0x55cc30fe1278 <col:8> col:8 implicit used constexpr operator= 'C &(C &&) noexcept' inline default trivial
|   |-ParmVarDecl 0x55cc30fe1388 <col:8> col:8 used 'C &&'
|   `-CompoundStmt 0x55cc310101c0 <col:8>
|     |-BinaryOperator 0x55cc31010168 <col:8> 'int' lvalue '='
|     | |-MemberExpr 0x55cc30fe1530 <col:8> 'int' lvalue ->x 0x55cc30fe0870
|     | | `-CXXThisExpr 0x55cc30fe1520 <col:8> 'C *' this
|     | `-ImplicitCastExpr 0x55cc31010150 <col:8> 'int' <LValueToRValue>
|     |   `-MemberExpr 0x55cc30fe14f0 <col:8> 'int' xvalue .x 0x55cc30fe0870
|     |     `-CXXStaticCastExpr 0x55cc30fe14c0 <col:8> 'C' xvalue static_cast<struct C &&> <NoOp>
|     |       `-DeclRefExpr 0x55cc30fe1490 <col:8> 'C' lvalue ParmVar 0x55cc30fe1388 '' 'C &&'
|     `-ReturnStmt 0x55cc310101b0 <col:8>
|       `-UnaryOperator 0x55cc31010198 <col:8> 'C' lvalue prefix '*' cannot overflow
|         `-CXXThisExpr 0x55cc31010188 <col:8> 'C *' this

#endif
