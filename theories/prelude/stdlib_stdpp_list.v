From bedrock.prelude Require Import base list.

(*
stdlib -> stdpp
combine -> zip
split -> unzip (below) or its definition.
*)

Definition unzip {A B} (l : list (A * B)) : list A * list B := (l.*1, l.*2).

Lemma combine_zip {A B} (l1 : list A) (l2 : list B) :
  combine l1 l2 = zip l1 l2.
Proof. done. Qed.

Lemma split_unzip {A B} (l : list (A * B)) :
  split l = unzip l.
Proof.
  rewrite /unzip; elim: l => [//|[a b] l IHl]; cbn.
  case_match. by simplify_eq.
Qed.

Lemma split_unzip' {A B} (l : list (A * B)) l1 l2 :
  (l1, l2) = split l ->
  (l1, l2) = unzip l.
Proof. by rewrite split_unzip. Qed.

Lemma split_alt {A B} (l : list (A * B)) l1 l2 :
  (l1, l2) = split l ->
  l1 = l.*1 ∧ l2 = l.*2.
Proof. rewrite split_unzip /unzip. naive_solver. Qed.
