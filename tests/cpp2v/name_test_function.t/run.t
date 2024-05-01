  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bedrock.auto.cpp.templates.mparser2.
  
  #[local] Open Scope bs_scope.
  
  Definition module_names : list Mname :=
    (
      (* Function fid() at $TESTCASE_ROOT/test.cpp:9:1 *) (Nglobal (Nfunction (nil) (Nf "fid") nil)) ::
  
      (* CXXConstructor fname::fname() at $TESTCASE_ROOT/test.cpp:11:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction (nil) Nctor nil)) ::
  
      (* CXXDestructor fname::~fname() at $TESTCASE_ROOT/test.cpp:12:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction (nil) Ndtor nil)) ::
  
      (* CXXMethod fname::operator++() at $TESTCASE_ROOT/test.cpp:17:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction (nil) (Nop OOPlusPlus) nil)) ::
  
      (* CXXConversion fname::operator int() at $TESTCASE_ROOT/test.cpp:18:5 *) (Nscoped (Nglobal (Nid "fname")) (Nfunction (nil) (Nop_conv Tint) nil)) ::
  
      (* Function operator""_lit(unsigned long long) at $TESTCASE_ROOT/test.cpp:20:1 *) (Nglobal (Nfunction (nil) (Nop_lit "_lit") (Tulonglong :: nil))) ::
  
      (* CXXDestructor extra::~extra() at $TESTCASE_ROOT/test.cpp:26:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (nil) Ndtor nil)) ::
  
      (* CXXMethod extra::args() at $TESTCASE_ROOT/test.cpp:32:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (nil) (Nf "args") nil)) ::
  
      (* CXXMethod extra::args(int, bool) at $TESTCASE_ROOT/test.cpp:33:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (nil) (Nf "args") (Tint :: Tbool :: nil))) ::
  
      (* CXXMethod extra::l() & at $TESTCASE_ROOT/test.cpp:34:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (Nlvalue :: nil) (Nf "l") nil)) ::
  
      (* CXXMethod extra::r() && at $TESTCASE_ROOT/test.cpp:35:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (Nrvalue :: nil) (Nf "r") nil)) ::
  
      (* CXXMethod extra::c() const at $TESTCASE_ROOT/test.cpp:36:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (Nconst :: nil) (Nf "c") nil)) ::
  
      (* CXXMethod extra::v() volatile at $TESTCASE_ROOT/test.cpp:37:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (Nvolatile :: nil) (Nf "v") nil)) ::
  
      (* CXXMethod extra::cvl() const volatile & at $TESTCASE_ROOT/test.cpp:38:5 *) (Nscoped (Nglobal (Nid "extra")) (Nfunction (Nconst :: Nvolatile :: Nlvalue :: nil) (Nf "cvl") nil)) ::
  
      (* CXXRecord fname at $TESTCASE_ROOT/test.cpp:10:1 *) (Nglobal (Nid "fname")) ::
  
      (* CXXRecord extra at $TESTCASE_ROOT/test.cpp:24:1 *) (Nglobal (Nid "extra")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
