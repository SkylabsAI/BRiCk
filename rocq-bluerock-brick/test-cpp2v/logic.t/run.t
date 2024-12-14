  $ . ../setup-project.sh
  $ dune build test.vo
  mpred_sep :
  ∀ {thread_info : biIndex} {_Σ : gFunctors}, mpred → mpred → mpredI
  
  mpred_sep is not universe polymorphic
  Arguments mpred_sep {thread_info _Σ} (P Q)%_bi_scope
  mpred_sep is transparent
  Expands to: Constant test.test.mpred_sep
  Declared in library test.test, line 6, characters 15-24
  rep_sep :
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ},
    Rep → Rep → RepI
  
  rep_sep is not universe polymorphic
  Arguments rep_sep {thread_info _Σ Σ} (P Q)%_bi_scope
  rep_sep is transparent
  Expands to: Constant test.test.rep_sep
  Declared in library test.test, line 7, characters 15-22
  _at
       : ptr → Rep → mpredI
  p |-> R
       : mpredI
  _offsetR
       : offset → Rep → RepI
  o |-> R
       : RepI
  1 goal
    
    σ : genv
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    R : Rep
    f, g : name
    o : offset
    p : ptr
    v : val
    ============================
    o ,, o_field σ f = o ,, o_field σ f
  1 goal
    
    σ : genv
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    R : Rep
    f, g : name
    o : offset
    p : ptr
    v : val
    ============================
    p |-> R = p |-> R
  1 goal
    
    σ : genv
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    R : Rep
    f, g : name
    o : offset
    p : ptr
    v : val
    ============================
    o |-> R = o |-> R
  _2 = p |-> o_field σ f |-> R
       : mpredI
  
  _2 uses section variables σ thread_info _Σ Σ R f p.
  _3 = p .[ "int" ! 0 ] |-> R
       : mpredI
  
  _3 uses section variables σ thread_info _Σ Σ R p.
  _4 = p |-> o_field σ f .[ "int" ! 0 ] |-> R
       : mpredI
  
  _4 uses section variables σ thread_info _Σ Σ R f p.
  _4a = p ,, o_field σ f |-> R
       : mpredI
  
  _4a uses section variables σ thread_info _Σ Σ R f p.
  1 goal
    
    σ : genv
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    R : Rep
    f, g : name
    o : offset
    p : ptr
    v : val
    ============================
    p ,, o_field σ f .[ "int" ! 0 ] = p ,, o_field σ f .[ "int" ! 0 ]
  _5 = p .[ "int" ! 0 ] .[ "int" ! 3 ] |-> R
       : mpredI
  
  _5 uses section variables σ thread_info _Σ Σ R p.
  _6 = p ,, o_field σ f .[ "int" ! 0 ] ,, o_field σ g |-> R
       : mpredI
  
  _6 uses section variables σ thread_info _Σ Σ R f g p.
  _7 =
  p ,, o_field σ g ,, o_field σ f .[ "int" ! 1 ] .[ "int" ! 0 ] ,, 
  o_field σ f |-> o_field σ f |-> R
       : mpredI
  
  _7 uses section variables σ thread_info _Σ Σ R f g p.
  _8 =
  p ,, o_field σ g ,, o_field σ f .[ "int" ! 1 ] .[ "int" ! 0 ] ,, 
  o_field σ f |-> .[ "int" ! 1 ] |-> R
       : mpredI
  
  _8 uses section variables σ thread_info _Σ Σ R f g p.
  _9 =
  o ,, o_field σ g ,, o_field σ f .[ "int" ! 1 ] .[ "int" ! 0 ] ,, 
  o_field σ f |-> R
       : RepI
  
  _9 uses section variables σ thread_info _Σ Σ R f g o.
  _11 = o .[ "int" ! 1 ] |-> R
       : RepI
  
  _11 uses section variables σ thread_info _Σ Σ R o.
  _14 = .[ "int" ! 1 ] |-> R
       : RepI
  
  _14 uses section variables σ thread_info _Σ Σ R.
  _16 = p .[ "int" ! 1 ] |-> o_field σ f |-> R
       : mpredI
  
  _16 uses section variables σ thread_info _Σ Σ R f p.
  b0 = p |-> R
       : mpredI
  
  b0 uses section variables thread_info _Σ Σ R p.
  b1 = o_field σ f |-> R
       : RepI
  
  b1 uses section variables σ thread_info _Σ Σ R f.
  b2 = p .[ "int" ! 1 ] |-> R
       : mpredI
  
  b2 uses section variables σ thread_info _Σ Σ R p.
  b3 = p .[ "int" ! 1 ] |-> o_field σ f |-> R
       : mpredI
  
  b3 uses section variables σ thread_info _Σ Σ R f p.
