  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bedrock.auto.cpp.templates.mparser2.
  
  #[local] Open Scope bs_scope.
  
  Definition module_names : list Mname :=
    (
      (* Function fid() at $TESTCASE_ROOT/test.cpp:9:1 *) (Nglobal (Nfunction function_qualifier.F_ (Nf "fid") nil Ar_Definite)) ::
  
      (* CXXConstructor fname::fname() at $TESTCASE_ROOT/test.cpp:11:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction function_qualifier.F_ Nctor nil Ar_Definite)) ::
  
      (* CXXDestructor fname::~fname() at $TESTCASE_ROOT/test.cpp:12:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction function_qualifier.F_ Ndtor nil Ar_Definite)) ::
  
      (* CXXMethod fname::operator++() at $TESTCASE_ROOT/test.cpp:17:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction function_qualifier.F_ (Nop OOPlusPlus) nil Ar_Definite)) ::
  
      (* CXXConversion fname::operator int() at $TESTCASE_ROOT/test.cpp:18:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction function_qualifier.F_ (Nop_conv Tint) nil Ar_Definite)) ::
  
      (* Function operator""_lit(unsigned long long) at $TESTCASE_ROOT/test.cpp:20:1 *) (Nglobal (Nfunction function_qualifier.F_ (Nop_lit "_lit") (Tulonglong :: nil) Ar_Definite)) ::
  
      (* CXXDestructor extra::~extra() at $TESTCASE_ROOT/test.cpp:26:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.F_ Ndtor nil Ar_Definite)) ::
  
      (* CXXMethod extra::args() at $TESTCASE_ROOT/test.cpp:32:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.F_ (Nf "args") nil Ar_Definite)) ::
  
      (* CXXMethod extra::args(int, bool) at $TESTCASE_ROOT/test.cpp:33:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.F_ (Nf "args") (Tint :: Tbool :: nil) Ar_Definite)) ::
  
      (* CXXMethod extra::l() & at $TESTCASE_ROOT/test.cpp:34:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.FL (Nf "l") nil Ar_Definite)) ::
  
      (* CXXMethod extra::r() && at $TESTCASE_ROOT/test.cpp:35:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.FR (Nf "r") nil Ar_Definite)) ::
  
      (* CXXMethod extra::c() const at $TESTCASE_ROOT/test.cpp:36:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.FC (Nf "c") nil Ar_Definite)) ::
  
      (* CXXMethod extra::v() volatile at $TESTCASE_ROOT/test.cpp:37:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.FV (Nf "v") nil Ar_Definite)) ::
  
      (* CXXMethod extra::cvl() const volatile & at $TESTCASE_ROOT/test.cpp:38:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction function_qualifier.FLCV (Nf "cvl") nil Ar_Definite)) ::
  
      (* CXXRecord fname at $TESTCASE_ROOT/test.cpp:10:1 *) (Nglobal (Nid "fname")) ::
  
      (* CXXRecord extra at $TESTCASE_ROOT/test.cpp:24:1 *) (Nglobal (Nid "extra")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
