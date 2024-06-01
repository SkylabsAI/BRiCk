  $ . ../setup-project.sh
  $ dune build test.vo
  Notation_Tptr_1 = {t: ptr<bool>}
       : type
  Notation_Tptr_2 = {t: ptr<{?: ty}>}
       : type
  
  Notation_Tptr_2 uses section variable ty.
  Notation_Tref_1 = {t: ref&<bool>}
       : type
  Notation_Tref_2 = {t: ref&<{?: ty}>}
       : type
  
  Notation_Tref_2 uses section variable ty.
  Notation_Trv_ref_1 = {t: ref&&<bool>}
       : type
  Notation_Trv_ref_2 = {t: ref&&<{?: ty}>}
       : type
  
  Notation_Trv_ref_2 uses section variable ty.
  Notation_Tref_Trv_ref = {t: ref&<ref&&<{?: ty}>>}
       : type
  
  Notation_Tref_Trv_ref uses section variable ty.
  Notation_Trv_ref_Tref = {t: ref&&<ref&<{?: ty}>>}
       : type
  
  Notation_Trv_ref_Tref uses section variable ty.
  Notation_void = {t: void}
       : type
  Notation_Tarray_1 = {t: nullptr_t[100]}
       : type
  Notation_Tarray_2 = {t: {?: ty}[n]}
       : type
  
  Notation_Tarray_2 uses section variables ty n.
  Notation_Tnamed_1 = {t: "foobarbaz"%cpp_name}
       : type
  Notation_Tnamed_2 = {t: nm}
       : type
  
  Notation_Tnamed_2 uses section variable nm.
  Notation_Tfunction_novariadic_noargs_1 =
  {t: extern CC_C ???() -> void}
       : type
  Notation_Tfunction_novariadic_noargs_2 =
  {t: extern CC_C ???() -> {?: rty}}
       : type
  
  Notation_Tfunction_novariadic_noargs_2 uses section variable rty.
  Notation_Tfunction_novariadic_args_nowrap_1 =
  {t: extern CC_C ???(bool, nullptr_t) -> void}
       : type
  Notation_Tfunction_novariadic_args_nowrap_2 =
  {t: extern CC_C ???({?: aty1}, void, {?: aty2}) -> {?: rty}}
       : type
  
  Notation_Tfunction_novariadic_args_nowrap_2 uses section variables
  rty aty1 aty2.
  Notation_Tfunction_novariadic_args_wrap =
  {t: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk"%cpp_name,
                      "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk"%cpp_name) -> void}
       : type
  Notation_Tfunction_variadic_noargs_1 =
  {t: extern CC_C ???()(...) -> void}
       : type
  Notation_Tfunction_variadic_noargs_2 =
  {t: extern CC_C ???()(...) -> {?: rty}}
       : type
  
  Notation_Tfunction_variadic_noargs_2 uses section variable rty.
  Notation_Tfunction_variadic_args_nowrap_1 =
  {t: extern CC_C ???(bool, nullptr_t)(...) -> void}
       : type
  Notation_Tfunction_variadic_args_nowrap_2 =
  {t: extern CC_C ???({?: aty1}, void, {?: aty2})(...) -> {?: rty}}
       : type
  
  Notation_Tfunction_variadic_args_nowrap_2 uses section variables
  rty aty1 aty2.
  Notation_Tfunction_variadic_args_wrap =
  {t: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk"%cpp_name,
                      "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk"%cpp_name)(...) -> void}
       : type
  Notation_Tbool = {t: bool}
       : type
  Notation_Tmember_pointer_1 =
  {t: ptr[{t: "foobarbaz"%cpp_name}]<char>}
       : type
  Notation_mut_1 = Qmut ({t: bool})
       : type
  Notation_mut_2 = Qmut (Qmut ({t: bool}))
       : type
  Notation_const_1 = Qconst ({t: bool})
       : type
  Notation_const_2 = Qconst ({t: ptr<{?: Qconst ({t: void})}>})
       : type
  Notation_volatile_1 = {t: volatile bool}
       : type
  Notation_volatile_2 = {t: volatile ptr<{?: Qconst ({t: void})}>}
       : type
  Notation_const_volatile_1 = Qconst_volatile ({t: bool})
       : type
  Notation_const_volatile_2 =
  Qconst_volatile ({t: ptr<{?: Qconst_volatile ({t: void})}>})
       : type
