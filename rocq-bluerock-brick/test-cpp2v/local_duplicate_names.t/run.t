  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make
  $ ls *.v | wc -l | sed -e 's/ //g'
  3

Compiling the generated Coq files.
  $ dune build
  File "./test_cpp.v", line 30, characters 0-7659:
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
