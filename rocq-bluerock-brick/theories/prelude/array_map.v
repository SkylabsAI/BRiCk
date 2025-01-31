Require Import Stdlib.Array.PArray.
Require Import BinNatDef.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import bedrock.prelude.base.

Module Type KEY.
  Parameter key : Type.
  Declare Instance inh : Inhabited key.
  Parameter compare : key -> key -> comparison.
End KEY.

(* NOTE: using this seems to be **significantly** slower *)
#[global,program] Instance int_eq_dec : EqDecision int :=
  fun a b => match (a =? b)%uint63 as X return (a =? b)%uint63 = X -> _ with
             | true => fun _ => left _
             | _ => fun _ => right _
             end eq_refl.
Next Obligation. apply eqb_correct. Qed.
Next Obligation. intros; intro. eapply eqb_complete in H. congruence. Qed.

Module map (Import K : KEY).
  Section with_value.
    Context {elt : Type}.

    (** The representation of arrays is two parallel arrays, one with keys and one with values.
        This representation is more space efficient than a single array of pairs (in expectation).

        Additionally, thre should be a proof that the two arrays are the same length and that
        the key array is sorted.
     *)
    Record t := mk
      { keys : array key
      ; values : array elt
      }.

    Definition empty {inh : Inhabited elt} : t :=
      {| keys := PArray.make 0 inhabitant
       ; values := PArray.make 0 inhabitant |}.

    #[local] Fixpoint find_key (a : array key) (needle : key) (fuel : nat) (min max : int)
      : option int :=
      if (max =? min)%uint63 then None
      else
        let mid := (min + (max - min) / 2)%uint63 in
        let k_mid := PArray.get a mid in
        let next min max :=
          match fuel with
          | O => None
          | S fuel => find_key a needle fuel min max
          end
        in
        match compare needle k_mid with
        | Eq => Some mid
        | Lt => next min mid
        | Gt => next (mid + 1)%uint63 max
        end.

    Definition find (needle : key) (m : t) : option elt :=
      let max := PArray.length m.(keys) in
      (* Guard fuel on [m.(keys)] *)
      let fuel := if (max =? 0)%uint63 then 0 else 63 in
      match find_key m.(keys) needle fuel 0 max with
      | None => None
      | Some idx => Some (PArray.get m.(values) idx)
      end.

    #[local] Fixpoint fill (ls : list (key * elt)) (i : int)
      (keys : array key) (values : array elt) : array key * array elt :=
      match ls with
      | nil => (keys, values)
      | (k, v) :: ls =>
          fill ls (i + 1)%uint63 (PArray.set keys i k) (PArray.set values i v)
      end.

    Definition of_sorted_list {inh : Inhabited elt} (ls : list (key * elt)) : t :=
      let l := List.fold_left (fun a _ => a + 1)%uint63 ls 0%uint63 in
      let keys : array key := PArray.make l inhabitant in
      let values : array elt := PArray.make l inhabitant in
      let '(keys, values) := fill ls 0%uint63 keys values in
      mk keys values.

    #[local]
    Fixpoint fold_to {A} (f : key -> elt -> A -> A) (m : t) (count : nat) (i : int) (acc : A) : A :=
      match count with
      | 0 => acc
      | S count => fold_to f m count (i + 1)%uint63 (f (PArray.get m.(keys) i) (PArray.get m.(values) i) acc)
      end.

    Definition fold {A} (f : key -> elt -> A -> A) (m : t) (acc : A) : A :=
      fold_to f m (Z.to_nat $ to_Z $ PArray.length m.(keys)) 0 acc.

    #[local]
    Fixpoint elements_to (m : t) (count : nat) (i : int) (acc : list (key * elt)) : list (key * elt) :=
      match count with
      | 0 => acc
      | S count => elements_to m count (i - 1)%uint63 ((PArray.get m.(keys) i, PArray.get m.(values) i) :: acc)
      end.

    Definition elements (m : t) : list (key * elt) :=
      elements_to m (Z.to_nat $ to_Z $ PArray.length m.(keys)) (PArray.length m.(keys) - 1)%uint63 nil.

    #[local]
    Fixpoint find_any_to (f : key -> elt -> bool) (m : t) (count : nat) (i : int) : bool :=
      match count with
      | 0 => false
      | S count =>
          if f (PArray.get m.(keys) i) (PArray.get m.(values) i) then true
          else find_any_to f m count (i - 1)%uint63
      end.

    Definition find_any (f : key -> elt -> bool) (m : t) :=
      find_any_to f m (Z.to_nat $ to_Z $ PArray.length m.(keys)) (PArray.length m.(keys) - 1)%uint63.

    Definition copy (m : t) : t :=
      mk (PArray.copy m.(keys)) (PArray.copy m.(values)).

    Definition cardinal (m : t) : nat :=
      Z.to_nat $ to_Z $ PArray.length m.(keys).

    Lemma cardinal_1 : forall m, cardinal m = length (elements m).
    Proof. Admitted.

    Definition MapsTo (k : key) (v : elt) (m : t) :=
      find k m = Some v.

    Lemma find_1 : forall x e (m : t), MapsTo x e m -> find x m = Some e.
    Proof. done. Qed.
    Lemma find_2 : forall x e m, find x m = Some e -> MapsTo x e m.
    Proof. done. Qed.

    Lemma find_any_ok b (m : t) :
      if find_any b m
      then exists k v, MapsTo k v m /\ b k v = true
      else forall k v, MapsTo k v m -> b k v = false.
    Proof. Admitted.

  End with_value.
  #[global] Arguments t : clear implicits.
End map.
