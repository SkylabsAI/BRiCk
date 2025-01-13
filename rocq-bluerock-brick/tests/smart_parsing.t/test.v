Require Import bedrock.lang.cpp.syntax.
Require test.test_cpp.

Module notation_wrapper.

(* TODO: this needs to be put in the [_cpp.v] file *)
Definition parser x := parser.parse_name_with test_cpp.module (BS.parse x).
Definition printer n := (match printer.print_name n with
                         | None => None
                         | Some x => Some (BS.print x)
                         end).
String Notation core.name parser printer : cpp_name_scope.

End notation_wrapper.

(* Global notation is used without [Import notation_wrapper.], type aliases don't work. *)
Goal "test(INT, SINT)"%cpp_name = (Nglobal (Nfunction function_qualifiers.N (Nf "test") (Tint :: Tint :: nil))).
Proof. Fail reflexivity. Abort.

Import notation_wrapper.

(* [Import notation_wrapper.] shadows notation and enables support for aliases. *)
Goal "test(INT, SINT)"%cpp_name = (Nglobal (Nfunction function_qualifiers.N (Nf "test") (Tint :: Tint :: nil))).
Proof. reflexivity. Qed.

Goal "test(int, int)"%cpp_name = (Nglobal (Nfunction function_qualifiers.N (Nf "test") (Tint :: Tint :: nil))).
Proof. reflexivity. Qed.

Goal "test_e(enum E)"%cpp_name = (Nglobal (Nfunction function_qualifiers.N (Nf "test_e") (Tenum "E" :: nil))).
Proof. reflexivity. Qed.

(* The use of [enum] is optional *)
Goal "test_e(E)"%cpp_name = (Nglobal (Nfunction function_qualifiers.N (Nf "test_e") (Tenum "E" :: nil))).
Proof. reflexivity. Qed.


(* unknown symbol within the TU
   NOTE: this could be a parsing error, but it requires that we remove the default parser.
 *)
Goal "test_e()"%cpp_name = (Nglobal (Nfunction function_qualifiers.N (Nf "test_e") nil)).
Proof. reflexivity. Qed.
