  $ . ../../setup-name-test.sh
  $ name_test test.cpp
  # cpp2v --name-test=test_17_name_test.v test.cpp -- -std=c++17
  # scrub test_17_name_test.v
  Require Import bedrock.auto.cpp.templates.mparser2.
  
  #[local] Open Scope bs_scope.
  
  Definition module_names : list Mname :=
    (
      (* CXXRecord (anonymous namespace)::inhabit_ns at $TESTCASE_ROOT/test.cpp:10:5 *) (Nscoped (Nglobal (Nanon 0)) (Nid "inhabit_ns")) ::
  
      (* CXXConstructor container::container() at $TESTCASE_ROOT/test.cpp:13:5 *) (Nscoped (Nglobal (Nid "container")) (Nfunction function_qualifier.F_ Nctor nil Ar_Definite)) ::
  
      (* CXXDestructor container::~container() at $TESTCASE_ROOT/test.cpp:14:5 *) (Nscoped (Nglobal (Nid "container")) (Nfunction function_qualifier.F_ Ndtor nil Ar_Definite)) ::
  
      (* CXXRecord container at $TESTCASE_ROOT/test.cpp:12:1 *) (Nglobal (Nid "container")) ::
  
      (* CXXRecord container::(anonymous struct at $TESTCASE_ROOT/test.cpp:20:5) at $TESTCASE_ROOT/test.cpp:20:5 *) (Nscoped (Nglobal (Nid "container")) (Nanon 0)) ::
  
      (* CXXConstructor container::(anonymous struct)::(anonymous struct at $TESTCASE_ROOT/test.cpp:20:5)() at $TESTCASE_ROOT/test.cpp:20:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 0)) (Nfunction function_qualifier.F_ Nctor nil Ar_Definite)) ::
  
      (* CXXConstructor container::(anonymous struct)::(anonymous struct at $TESTCASE_ROOT/test.cpp:20:5)(const (anonymous struct at $TESTCASE_ROOT/test.cpp:20:5) &) at $TESTCASE_ROOT/test.cpp:20:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 0)) (Nfunction function_qualifier.F_ Nctor ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "container")) (Nanon 0))))) :: nil) Ar_Definite)) ::
  
      (* CXXMethod container::(anonymous struct)::operator=(const (anonymous struct at $TESTCASE_ROOT/test.cpp:20:5) &) at $TESTCASE_ROOT/test.cpp:20:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 0)) (Nfunction function_qualifier.F_ (Nop OOEqual) ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "container")) (Nanon 0))))) :: nil) Ar_Definite)) ::
  
      (* CXXConstructor container::(anonymous struct)::(anonymous struct at $TESTCASE_ROOT/test.cpp:20:5)((anonymous struct at $TESTCASE_ROOT/test.cpp:20:5) &&) at $TESTCASE_ROOT/test.cpp:20:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 0)) (Nfunction function_qualifier.F_ Nctor ((Trv_ref (Tnamed (Nscoped (Nglobal (Nid "container")) (Nanon 0)))) :: nil) Ar_Definite)) ::
  
      (* CXXMethod container::(anonymous struct)::operator=((anonymous struct at $TESTCASE_ROOT/test.cpp:20:5) &&) at $TESTCASE_ROOT/test.cpp:20:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 0)) (Nfunction function_qualifier.F_ (Nop OOEqual) ((Trv_ref (Tnamed (Nscoped (Nglobal (Nid "container")) (Nanon 0)))) :: nil) Ar_Definite)) ::
  
      (* CXXDestructor container::(anonymous struct)::~(anonymous struct at $TESTCASE_ROOT/test.cpp:20:5)() at $TESTCASE_ROOT/test.cpp:20:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 0)) (Nfunction function_qualifier.F_ Ndtor nil Ar_Definite)) ::
  
      (* CXXRecord container::(anonymous union at $TESTCASE_ROOT/test.cpp:24:5) at $TESTCASE_ROOT/test.cpp:24:5 *) (Nscoped (Nglobal (Nid "container")) (Nanon 1)) ::
  
      (* CXXConstructor container::(anonymous union)::(anonymous union at $TESTCASE_ROOT/test.cpp:24:5)(const (anonymous union at $TESTCASE_ROOT/test.cpp:24:5) &) at $TESTCASE_ROOT/test.cpp:24:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 1)) (Nfunction function_qualifier.F_ Nctor ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "container")) (Nanon 1))))) :: nil) Ar_Definite)) ::
  
      (* CXXConstructor container::(anonymous union)::(anonymous union at $TESTCASE_ROOT/test.cpp:24:5)((anonymous union at $TESTCASE_ROOT/test.cpp:24:5) &&) at $TESTCASE_ROOT/test.cpp:24:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 1)) (Nfunction function_qualifier.F_ Nctor ((Trv_ref (Tnamed (Nscoped (Nglobal (Nid "container")) (Nanon 1)))) :: nil) Ar_Definite)) ::
  
      (* CXXDestructor container::(anonymous union)::~(anonymous union at $TESTCASE_ROOT/test.cpp:24:5)() at $TESTCASE_ROOT/test.cpp:24:5 *) (Nscoped (Nscoped (Nglobal (Nid "container")) (Nanon 1)) (Nfunction function_qualifier.F_ Ndtor nil Ar_Definite)) ::
  
      (* Enum (unnamed enum at $TESTCASE_ROOT/test.cpp:28:1) at $TESTCASE_ROOT/test.cpp:28:1 *) (Nglobal (Nanon 1)) ::
  
      (* EnumConstant inhabit_e at $TESTCASE_ROOT/test.cpp:28:8 *) (Nglobal (Nid "inhabit_e")) ::
      nil).
  
  Definition template_names : list Mname :=
    (nil).
