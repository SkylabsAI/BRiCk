  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make
  $ ls *.v | wc -l | sed -e 's/ //g'
  3

Compiling the generated Coq files.
  $ dune build
  File "./test_cpp.v", line 6, characters 0-8277:
  Warning:
  Duplicate symbols found![("test()::T"%cpp_name, inl (Gtypedef "int"));
                           ("test()::T"%cpp_name,
                            inl
                              (Gstruct
                                 {|
                                   s_bases := [];
                                   s_fields := [];
                                   s_virtuals := [];
                                   s_overrides := [];
                                   s_dtor := "test()::T::~T()";
                                   s_trivially_destructible := true;
                                   s_delete := None;
                                   s_layout := POD;
                                   s_size := 1;
                                   s_alignment := 1
                                 |}))]
       = true
       : supported.check.M
  $ cat test_cpp.v
  Require Import bluerock.lang.cpp.parser.
  
  #[local] Open Scope pstring_scope.
  
  Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
  cpp.prog module
    abi Little
    defns
  
      (Dtypedef (Nglobal (Nid "__int128_t")) Tint128_t)
      (Dtypedef (Nglobal (Nid "__uint128_t")) Tuint128_t)
      (Dtypedef (Nglobal (Nid "__NSConstantString")) (Tnamed (Nglobal (Nid "__NSConstantString_tag"))))
      (Dtypedef (Nglobal (Nid "__builtin_ms_va_list")) (Tptr Tchar))
      (Dtypedef (Nglobal (Nid "__builtin_va_list")) (Tarray (Tnamed (Nglobal (Nid "__va_list_tag"))) 1))
      (Dfunction (Nglobal (Nfunction function_qualifiers.N "test" nil))
        (Build_Func Tvoid
          nil CC_C Ar_Definite
          (Some (Impl
              (Sseq (
                  (Sdecl (nil)) ::
                  (Sdecl (
                      (Dvar "x0" Tint None) :: nil)) ::
                  (Sseq (
                      (Sdecl (nil)) ::
                      (Sdecl (
                          (Dvar "x1" Tchar None) :: nil)) ::
                      (Sseq (
                          (Sdecl (nil)) ::
                          (Sdecl (
                              (Dvar "x2" (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))
                                (Some
                                  (Econstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor nil)) nil (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))))) :: nil)) :: nil)) ::
                      (Sseq (
                          (Sdecl (nil)) ::
                          (Sdecl (
                              (Dvar "x3" (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))
                                (Some
                                  (Econstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor nil)) nil (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))))) :: nil)) :: nil)) :: nil)) ::
                  (Sseq (
                      (Sdecl (nil)) ::
                      (Sdecl (
                          (Dvar "x4" Tlonglong None) :: nil)) :: nil)) ::
                  (Sdecl (
                      (Dvar "x5" Tint None) :: nil)) :: nil))))))
      (Dtypedef (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) Tint)
      (Dtypedef (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T'0")) Tchar)
      (Dstruct (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))
        (Some
          (Build_Struct nil
            nil (nil) (nil) (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) Ndtor) true None
            POD 1 1)))
      (Dconstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor nil))
        (Build_Ctor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) nil CC_C Ar_Definite
          (Some
            (UserDefined (nil,
              (Sseq (nil)))))))
      (Dconstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil)))
        (Build_Ctor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (((localname.anon 0), (Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))))) :: nil) CC_C Ar_Definite None))
      (Dmethod (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nop function_qualifiers.N OOEqual ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil))) false
        (Build_Method (Tref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) QM (((localname.anon 0), (Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))))) :: nil) CC_C Ar_Definite (Some Defaulted)))
      (Dconstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor ((Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) :: nil)))
        (Build_Ctor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (((localname.anon 0), (Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil) CC_C Ar_Definite None))
      (Dmethod (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nop function_qualifiers.N OOEqual ((Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) :: nil))) false
        (Build_Method (Tref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) QM (((localname.anon 0), (Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil) CC_C Ar_Definite (Some Defaulted)))
      (Ddestructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) Ndtor)
        (Build_Dtor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) CC_C (Some Defaulted)))
      (Dstruct (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))
        (Some
          (Build_Struct nil
            nil (nil) (nil) (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) Ndtor) true None
            POD 1 1)))
      (Dconstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor nil))
        (Build_Ctor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) nil CC_C Ar_Definite
          (Some
            (UserDefined (nil,
              (Sseq (nil)))))))
      (Dconstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil)))
        (Build_Ctor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (((localname.anon 0), (Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))))) :: nil) CC_C Ar_Definite None))
      (Dmethod (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nop function_qualifiers.N OOEqual ((Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil))) false
        (Build_Method (Tref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) QM (((localname.anon 0), (Tref (Qconst (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))))) :: nil) CC_C Ar_Definite (Some Defaulted)))
      (Dconstructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nctor ((Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) :: nil)))
        (Build_Ctor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (((localname.anon 0), (Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil) CC_C Ar_Definite None))
      (Dmethod (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) (Nop function_qualifiers.N OOEqual ((Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) :: nil))) false
        (Build_Method (Tref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")))) (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) QM (((localname.anon 0), (Trv_ref (Tnamed (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T"))))) :: nil) CC_C Ar_Definite (Some Defaulted)))
      (Ddestructor (Nscoped (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) Ndtor)
        (Build_Dtor (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T")) CC_C (Some Defaulted)))
      (Dtypedef (Nscoped (Nglobal (Nfunction function_qualifiers.N "test" nil)) (Nid "T'3")) Tlonglong).
  
  Require bluerock.lang.cpp.syntax.typed.
  Succeed Example well_typed : typed.decltype.check_tu module = trace.Success tt := ltac:(vm_compute; reflexivity).
