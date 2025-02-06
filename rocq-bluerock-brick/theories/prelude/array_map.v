Require Import Stdlib.Array.PArray.
Require Import BinNatDef.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import bedrock.prelude.base.

Module Uint63_Fast.

    (* Faster than [to_Z], probably only for small-ish integers *)
    Fixpoint to_Z_zero_rec (n : nat) (i : int) {struct n} : Z :=
      if is_zero i then 0%Z else
      match n with
      | O => 0%Z
      | S n0 => (if is_even i then Z.double else Z.succ_double) (to_Z_zero_rec n0 (i >> 1)%uint63)
      end.
    Definition to_Z_zero := to_Z_zero_rec Uint63.size.
    Definition to_Z_zero' := Eval lazy [to_Z_zero_rec Uint63.size] in to_Z_zero_rec Uint63.size.


    Definition to_Z_rec_shift (i : int) : Z :=
      (fix go n k :=
         match n with
         | O => 0%Z
         | S n0 => (if is_even (i >> k) then Z.double else Z.succ_double) (go n0 (k - 1)%uint63)
         end) Uint63.size 62%uint63.
    Definition to_Z_shift := to_Z_rec_shift.
    Definition to_Z_shift' := Eval lazy [to_Z_rec_shift Uint63.size Uint63.sub] in to_Z_rec_shift.

    Definition is_even_at (i : int) (bit : int) :=
      (i land 1 << bit =? 0)%uint63.

    Definition to_Z_rec_shift_at (i : int) : Z :=
      (fix go n k :=
         match n with
         | O => 0%Z
         | S n0 => (if is_even_at i (62-k) then Z.double else Z.succ_double) (go n0 (k - 1)%uint63)
         end) Uint63.size 62%uint63.
    Definition to_Z_shift_at := to_Z_rec_shift_at.
    Definition to_Z_shift_at' := Eval lazy [to_Z_rec_shift_at Uint63.size Uint63.sub is_even_at Uint63.lsl] in to_Z_rec_shift_at.


    Definition to_Z_rec_cps (i : int) : Z :=
      (fix go n k cont :=
         match n with
         | O => cont 0%Z
         | S n0 =>
             go n0 (k + 1)%uint63 $ fun z =>
             (if is_even_at i (62-k) then
                Z.double
              else
                Z.succ_double) $ cont z
         end) Uint63.size 0%uint63 (fun z => z).
    Definition to_Z_cps := to_Z_rec_cps.
    Definition to_Z_cps' := Eval lazy [to_Z_rec_cps Uint63.size Uint63.sub Uint63.add is_even_at Uint63.lsl] in to_Z_rec_cps.



    (* highest bit in [0..62] *)
    Definition zeros_below (i : int) (highest_bit : int) :=
      (i land (max_int >> (63-highest_bit)) =? 0)%uint63.

    Definition to_Z_rec_at_zero (i : int) : Z :=
      (fix go n k :=
         if zeros_below i k then 0%Z else
         match n with
         | O => 0%Z
         | S n0 => (if is_even_at i (62-k) then Z.double else Z.succ_double) (go n0 (k - 1)%uint63)
         end) Uint63.size 62%uint63.
    Definition to_Z_at_zero := to_Z_rec_at_zero.
    Definition to_Z_at_zero' :=
      Eval lazy [
          to_Z_rec_at_zero Uint63.size Uint63.sub is_even_at
          Uint63.lsl Uint63.lsr
          zeros_below
          Uint63.max_int
          opp
        ] in to_Z_rec_at_zero.


    Definition zeros_above (i : int) (highest_bit : int) :=
      (i land (max_int << (highest_bit)) =? 0)%uint63.

    (* Definition to_pos_rec (i : int) : positive := *)
    (*   (fix go n k c := *)
    (*      if zeros_above i (k+1) then c xH else *)
    (*      match n with *)
    (*      | O => c xH *)
    (*      | S n0 => *)
    (*          (go n0 (k + 1)%uint63) *)
    (*            (fun p => c $ (if (is_even_at i k) then xO p else xI p)) *)
    (*      end) Uint63.size 0%uint63 (fun x => x). *)

    Definition to_pos_rec (i : int) : nat -> int -> positive :=
      (fix go n k :=
         match n with
         | O => xH
         | S n0 =>
             if zeros_above i (k+1) then xH else
             (if is_even_at i k then
              xO
             else
              xI) $ go n0 (k + 1)%uint63
         end).

    Definition to_Z_pos (i : int) :=
      if (i =? 0)%uint63 then 0%Z else Z.pos $ to_pos_rec i Uint63.size 0%uint63.

    Require Import Stdlib.micromega.ZifyUint63.

    Lemma decide_bounded (P : int -> Prop) `{P_dec : forall x, Decision (P x)} :
      Decision (exists x, P x).
    Proof.
      suff: (Decision (exists x, x <=? max_int = true /\ P x)%uint63).
      - move => [H|H]; [left|right].
        + destruct H as [x [Hx H]].
          exists x. auto.
        + move => H'. apply: H. destruct H' as [x H]. exists x.
          split; [lia|done].
      - pose m := to_nat max_int.
        have Hm : (m <= to_nat max_int)%nat by lia.
        have ->: max_int = of_nat m by lia.
        elim: m Hm => [|{}m IH] Hm.
        + case: (P_dec 0%uint63) => [H0|H0].
          * left. exists 0%uint63. split; [lia|done].
          * right. move => [x [Hx HP]].
            apply: H0.
            by have ->: (0 = x)%uint63 by lia.
        + case: (P_dec (of_nat (S m))) => [HPm|HPm].
          * left. exists (of_nat (S m)). split; [lia|done].
          * case: (IH ltac:(lia)) => [{}IH|{}IH].
            { left. destruct IH as [x [IHx IH]]. exists x.
              split; [lia|done]. }
            { right. intros H. apply: IH. destruct H as [x [Hxm Hx]].
              case H: (x =? of_nat (S m))%uint63.
              { exfalso. apply HPm. by have ->: (of_nat (S m) = x) by lia. }
              { exists x; split; [lia|done]. }
            }
    Qed.

    Lemma brute_force P d :
      nat_rect (fun i => Prop) (P 0) (fun n acc => P (S n) /\ acc) d ->
      forall x, x <= d -> P x.
    Proof.
      induction d.
      - simpl. move => H0 x Hx. by have ->: x = 0 by lia.
      - simpl. move => [H1 H2] x Hx.
        case Hx': (x =? S d)%nat.
        { by have ->: x = S d by lia. }
        apply IHd; [done|lia].
    Qed.

    Lemma bit_max_int b :
      (b <? digits)%uint63 = true ->
      bit max_int b = true.
    Proof.
      have ->: digits = of_nat 63 by lia.
      move => H.
      have Hb: b = of_nat (to_nat b) by lia.
      have Hb': (to_nat b <= 63)%nat by lia.
      move: H. rewrite {}Hb. move: (to_nat b) Hb' => {}b Hb Hb'.
      refine (brute_force (fun x => bit max_int (of_nat x) = true) 62 _ _ _); [|lia].
      vm_compute; by repeat split.
    Qed.

    Lemma zeros_above_false i j:
      zeros_above i j = false <->
      exists k, (to_Z j <= to_Z k < to_Z digits)%Z /\ bit i k = true.
    Proof.
      split.
      - rewrite /zeros_above.
        move/Uint63.eqb_false_spec.
        simpl. rewrite -/max_int.
        set P := (fun k => _ /\ _).
        have ? : forall x, Decision (P x).
        { intros. apply and_dec; apply _. }
        case: (decide_bounded P).
        { eauto. }
        intros Hx Hi.
        exfalso.
        apply: Hi.
        apply bit_ext => b.
        rewrite land_spec bit_0.
        case Hb: (digits <=? b)%uint63.
        { by rewrite bit_M // andb_false_l bit_0. }
        rewrite bit_lsl.
        case_match; [lia|].
        rewrite bit_max_int; [|lia].
        rewrite andb_true_r.
        have {}Hx: forall x, P x -> False.
        { move => x Hx'. apply: Hx. eauto. }
        specialize (Hx b). unfold P in Hx.
        apply not_true_is_false => Hib.
        apply: Hx.
        split; [lia|done].
      - move => [b [Hjb Hib]].
        rewrite /zeros_above.
        apply/Uint63.eqb_false_spec.
        move/(f_equal (fun i => bit i b)).
        rewrite land_spec.
        case Hb: (digits <=? b)%uint63; [lia|].
        rewrite bit_lsl.
        case_match; [lia|].
        rewrite bit_max_int; [|lia].
        by rewrite andb_true_r Hib bit_0.
    Qed.

    Lemma bit_ext' (i j : int) :
      (i =? j = true)%uint63 -> forall k, bit i k = bit j k.
    Proof.
      move/Uint63.eqb_spec => ->. done.
    Qed.

    Lemma zeros_above_true i j:
      zeros_above i j = true ->
      forall k, (j <=? k = true)%uint63 -> (k <? digits = true)%uint63 -> bit i k = false.
    Proof.
      rewrite /zeros_above.
      move => /bit_ext' => H k Hjk Hkd.
      rewrite -(bit_0 k).
      specialize (H k%uint63).
      move: H.
      rewrite land_spec.
      rewrite bit_lsl.
      case H: (_ || _); [lia|].
      apply orb_false_iff in H.
      rewrite bit_max_int; [|lia].
      by rewrite andb_true_r.
    Qed.

    Lemma zeros_above_true_2 i j:
      (j <? digits = true)%uint63 ->
      (forall k, (j <=? k = true)%uint63 -> (k <? digits = true)%uint63 -> bit i k = false) ->
      zeros_above i j = true.
    Proof.
      move => H1 H2.
      rewrite /zeros_above.
      apply Uint63.eqb_spec. apply bit_ext => b.
      rewrite bit_0.
      rewrite land_spec.
      rewrite bit_lsl.
      case_match; [lia|].
      rewrite bit_max_int; [|lia].
      rewrite andb_true_r.
      apply: H2; lia.
    Qed.

    Lemma zeros_above_true_shift i j:
      zeros_above i j = true ->
      (i >> j = 0)%uint63.
    Proof.
      move/zeros_above_true => H.
      apply bit_ext => b.
      rewrite bit_0.
      rewrite bit_lsr.
      case_match; [|reflexivity].
      case Hb: (digits <=? j + b)%uint63.
      { by rewrite bit_M. }
      rewrite H; lia.
    Qed.

    Lemma bit_land_1_lsr i j:
      (j <? digits)%uint63 = true ->
      ((i >> j) land 1 =? 0)%uint63 = ~~ bit i j.
    Proof.
      pose k := to_nat j.
      have ->: j = of_nat k by lia.
      intros H.
      have Hk: k < 63 by lia.
      clear H.
      move: {j} k Hk i.
      elim => [|k IH] Hk i.
      - simpl. rewrite lsr_0_r.
        have := is_even_bit i.
        by cbn => ->.
      - intros.
        have ->: (of_nat (S k) = of_nat k + 1)%uint63 by lia.
        rewrite -bit_half; [|lia].
        rewrite -IH; [|lia].
        rewrite lsr_add.
        case_match; [|lia].
        f_equal.
        f_equal.
        f_equal.
        lia.
    Qed.

    Lemma to_Z_rec_0 n : to_Z_rec n 0%uint63 = 0.
    Proof.
      induction n.
      - done.
      - cbn.
        rewrite IHn.
        lia.
    Qed.

    Lemma is_even_at_is_even i j:
      (j <? digits = true)%uint63 ->
      is_even_at i j = is_even (i >> j).
    Proof.
      intros.
      rewrite /is_even_at/is_even/is_zero/=.
      case Hea: (_ =? 0)%uint63 => //;
      case He: (_ =? 0)%uint63 => //.
      - rewrite bit_land_1_lsr in He; [|lia].
        exfalso.
        have {Hea} := (bit_ext' _ _ Hea j).
        rewrite bit_0 -{}He.
        rewrite land_spec.
        rewrite bit_lsl.
        case_match; [lia|].
        have ->: (j - j = 0)%uint63 by lia.
        rewrite andb_true_r. by case: (bit _ _).
      - exfalso.
        rewrite bit_land_1_lsr in He; [|lia].
        apply Uint63.eqb_false_spec in Hea.
        apply Hea.
        apply bit_ext => b.
        apply eq_sym in He.
        apply negb_sym in He.
        rewrite land_spec.
        rewrite bit_lsl.
        case_match.
        { by rewrite andb_false_r bit_0. }
        rewrite bit_1. case Hj: (_ =? 0)%uint63.
        { have ->: (b = j) by lia. by rewrite He bit_0. }
        { by rewrite andb_false_r bit_0. }
    Qed.

    Lemma to_Z_pos_rec_spec i :
      to_Z_pos i = Uint63.to_Z i.
    Proof.
      unfold to_Z_pos.
      case: (eqbP i 0)%uint63 => H.
      { by have ->: (i = of_Z 0) by lia. }
      unfold Uint63.to_Z.
      set x := 0%uint63.
      have : forall j, (0 <= to_Z j <= to_Z x)%Z -> zeros_above i j = false.
      { intros. have ? : j = 0%uint63 by lia. subst.
        rewrite /zeros_above lsl0_r.
        apply eqb_false_spec.
        move => Hi. 
        apply H. rewrite -{}Hi.
        f_equal.
        apply bit_ext => b.
        rewrite land_spec.
        case Hb: (digits <=? b)%uint63.
        { by rewrite !bit_M. }
        rewrite bit_max_int; [|lia].
        by rewrite andb_true_r.
      }

      have ->: x = (63 - of_nat (Uint63.size))%uint63 by done.
      set j := {3}i.
      have ->: j = (i >> (63 - of_nat (Uint63.size)))%uint63 by rewrite lsr_0_r.
      set n := Uint63.size.
      have Hn : n <= 63 by done.
      clearbody n. clear x j.
      induction n => Hz.
      - cbn. simpl.
        specialize (Hz 63%uint63 ltac:(lia)).
        cbn in Hz.
        rewrite land0_r in Hz. lia.
      - unfold to_pos_rec.
        case Hza: (zeros_above i (63 - of_nat (S n) + 1)).
        + cbn.
          have: bit i (63 - of_nat (S n)) = true.
          { destruct (proj1 (zeros_above_false _ _) (Hz (63 - of_nat (S n))%uint63 ltac:(lia)))
              as [b [Hb1 Hb2]].
            case: (Uint63.eqbP b (63 - of_nat (S n)))%uint63 => Hb.
            { move/(f_equal of_Z): Hb. rewrite !of_to_Z => ?. by subst. }
            rewrite (zeros_above_true _ _ Hza b) in Hb2; [done|lia|lia].
          }
          rewrite bit_land_1_lsr; [|lia].
          move => ->.
          rewrite zeros_above_true_shift; [|].
          { by rewrite to_Z_rec_0. }
          apply zeros_above_true_2; [lia|].
          intros.
          rewrite bit_lsr.
          case_match; [|lia].
          case Ht: (digits <=? 63 - of_nat (S n) + k)%uint63.
          { rewrite bit_M; [done|lia]. }
          eapply zeros_above_true; [exact Hza|lia|lia].
        + rewrite -/(to_pos_rec _).
          case He: (is_even_at _ _).
          * cbn -[is_even].
            rewrite -is_even_at_is_even; [|lia].
            rewrite He.
            rewrite lsr_add.
            case Hle: (_ <=? _)%uint63; [|lia].
            move: Hza.
            have ->: (63 - of_nat (S n) + 1 = 63 - of_nat n)%uint63 by lia.
            move => Hza.
            rewrite -{}IHn; [|lia|]; last first.
            { move => j Hj.
              case Hj': (j =? 63 - of_nat n)%uint63.
              { apply Uint63.eqb_spec in Hj'. by subst. }
              { apply Hz. lia. }
            }
            lia.
          * cbn -[is_even].
            rewrite -is_even_at_is_even; [|lia].
            rewrite He.
            rewrite lsr_add.
            case Hle: (_ <=? _)%uint63; [|lia].
            move: Hza.
            have ->: (63 - of_nat (S n) + 1 = 63 - of_nat n)%uint63 by lia.
            move => Hza.
            rewrite -{}IHn; [|lia|]; last first.
            { move => j Hj.
              case Hj': (j =? 63 - of_nat n)%uint63.
              { apply Uint63.eqb_spec in Hj'. by subst. }
              { apply Hz. lia. }
            }
            lia.
    Qed.


    Definition to_Z_pos' :=
      Eval lazy [
          to_Z_pos
          to_pos_rec
          Uint63.size
          Uint63.sub
          Uint63.add
          is_even_at
          Uint63.lsl Uint63.lsr
          zeros_above
          Uint63.max_int
          opp
        ] in to_Z_pos.

    Instructions Eval cbn in to_Z_pos' 1000.          (*   929641 *)
    Instructions Eval cbn in to_Z_cps' 1000.          (*  1438046 *)
    Instructions Eval cbn in to_Z_shift_at' 1000.     (*  1444908 *)
    Instructions Eval cbn in to_Z_pos  1000.          (*  1580101 *)
    Instructions Eval cbn in to_Z_at_zero' 1000.      (*  1927441 *)
    Instructions Eval cbn in to_Z 1000.               (*  2658531 *)
    Instructions Eval cbn in to_Z_shift' 1000.        (*  6758395 *)
    Instructions Eval cbn in to_Z_shift_at 1000.      (* 11003813 *)
    Instructions Eval cbn in to_Z_shift 1000.         (* 15617117 *)
    Instructions Eval cbn in to_Z_at_zero 1000.       (* 17260218 *)
    Instructions Eval cbn in Uint63.to_Z 1000.        (* 18665195 *)
    Instructions Eval cbn in to_Z_cps 1000.           (* 42629956 *)

    Instructions Eval cbn in to_Z_shift_at' max_int.  (*  6687966 *)
    Instructions Eval cbn in to_Z_cps' max_int.       (*  6691650 *)
    Instructions Eval cbn in to_Z_pos' max_int.       (*  6971998 *)
    Instructions Eval cbn in to_Z_at_zero' max_int.   (*  7208922 *)
    Instructions Eval cbn in to_Z_shift' max_int.     (*  7329249 *)
    Instructions Eval cbn in to_Z_shift max_int.      (* 16188723 *)
    Instructions Eval cbn in to_Z_shift_at max_int.   (* 16248515 *)
    Instructions Eval cbn in to_Z_pos max_int.        (* 23770184 *)
    Instructions Eval cbn in Uint63.to_Z max_int.     (* 23912206 *)
    Instructions Eval cbn in to_Z_at_zero max_int.    (* 23994139 *)
    Instructions Eval cbn in to_Z max_int.            (* 34248352 *)
    Instructions Eval cbn in to_Z_cps max_int.        (* 47883930 *)


    Instructions Eval lazy in to_Z_shift_at' max_int. (*  5952206 *)
    Instructions Eval lazy in to_Z_cps' max_int.      (*  5956495 *)
    Instructions Eval lazy in to_Z_at_zero' max_int.  (*  6067052 *)
    Instructions Eval lazy in to_Z_pos' max_int.      (*  6091810 *)
    Instructions Eval lazy in to_Z_shift' max_int.    (*  6151919 *)
    Instructions Eval lazy in Uint63.to_Z max_int.    (*  6359392 *)
    Instructions Eval lazy in to_Z_shift max_int.     (*  6492338 *)
    Instructions Eval lazy in to_Z max_int.           (*  6565755 *)
    Instructions Eval lazy in to_Z_cps max_int.       (*  6643789 *)
    Instructions Eval lazy in to_Z_shift_at max_int.  (*  6799749 *)
    Instructions Eval lazy in to_Z_pos max_int.       (*  6902058 *)
    Instructions Eval lazy in to_Z_at_zero max_int.   (*  6990130 *)

End Uint63_Fast.
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


Module Type SEARCH (Import K : KEY).
  Parameter idx : Type.
  Parameter of_pos : positive -> idx.
  Parameter add : idx -> idx -> idx.
  Parameter zero : idx.
  Parameter succ : idx -> idx.

  Parameter haystack : Type.
  Parameter get : haystack -> idx -> key.
End SEARCH.

Module BinarySearch (Import K : KEY) (Import S : SEARCH K).

  Inductive bisection :=
  | Split (n : idx) : (unit -> bisection) -> (unit -> bisection) -> bisection
  | Here (n : idx) : bisection.

  Fixpoint bisect_pos (offset : idx) (p : positive) : bisection :=
    match p return bisection with
    | xH => Here offset
    | xI p =>
        let l _ := bisect_pos offset p in
        let r _ := bisect_pos (add offset (succ $ of_pos p))%N p in
        Split (add offset $ of_pos p) l r
    | xO p =>
        let l _ := bisect_pos offset p in
        let r _ := bisect_pos (add offset $ of_pos p)%N p in
        Split (add offset $ of_pos p) l r
    end.

  Definition bisect_N (n : N) : bisection :=
    match n with
    | N0 => Here zero
    | Npos p => bisect_pos zero p
    end.

  Definition binary_search (arr : haystack) (needle : key) : bisection -> option idx :=
    fix go b :=
      match b with
      | Here n =>
          let k' := get arr n in
          if compare needle k' is Eq then
            Some n
          else
            None
      | Split n l r =>
          let k' := get arr n in
          match compare needle k' with
          | Lt => go (l ())
          | Eq => Some n
          | Gt => go (r ())
          end
      end.
End BinarySearch.

Module map (Import K : KEY).

  Definition idx := int.
  Definition of_pos := of_pos.
  Definition add := add.
  Definition zero := 0%uint63.
  Definition succ := add 1%uint63.
  Definition haystack := array key.
  Definition get := @get key.
  Include BinarySearch K.

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

    Definition find_key (needle : key) (m : t) : option idx :=
      Eval lazy match iota beta delta [Z.to_N] in
      let len := Z.to_N (Uint63_Fast.to_Z_pos (PArray.length m.(keys))) in
      binary_search m.(keys) needle $ bisect_N len.

    Definition find (needle : key) (m : t) : option elt :=
      match find_key needle m with
      | Some i => Some (PArray.get m.(values) i)
      | None => None
      end.

    (* #[local] Fixpoint find_key (a : array key) (needle : key) (fuel : nat) (min max : int) *)
    (*   : option int := *)
    (*   if (max =? min)%uint63 then None *)
    (*   else *)
    (*     let mid := (min + (max - min) / 2)%uint63 in *)
    (*     let k_mid := PArray.get a mid in *)
    (*     let next min max := *)
    (*       match fuel with *)
    (*       | O => None *)
    (*       | S fuel => find_key a needle fuel min max *)
    (*       end *)
    (*     in *)
    (*     match compare needle k_mid with *)
    (*     | Eq => Some mid *)
    (*     | Lt => next min mid *)
    (*     | Gt => next (mid + 1)%uint63 max *)
    (*     end. *)

    (* Definition find (needle : key) (m : t) : option elt := *)
    (*   let max := PArray.length m.(keys) in *)
    (*   (* Guard fuel on [m.(keys)] *) *)
    (*   let fuel := if (max =? 0)%uint63 then 0 else 63 in *)
    (*   match find_key m.(keys) needle fuel 0 max with *)
    (*   | None => None *)
    (*   | Some idx => Some (PArray.get m.(values) idx) *)
    (*   end. *)

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
      fold_to f m (Z.to_nat $ Uint63_Fast.to_Z_pos $ PArray.length m.(keys)) 0 acc.

    #[local]
    Fixpoint elements_to (m : t) (count : nat) (i : int) (acc : list (key * elt)) : list (key * elt) :=
      match count with
      | 0 => acc
      | S count => elements_to m count (i - 1)%uint63 ((PArray.get m.(keys) i, PArray.get m.(values) i) :: acc)
      end.

    Definition elements (m : t) : list (key * elt) :=
      elements_to m (Z.to_nat $ Uint63_Fast.to_Z_pos $ PArray.length m.(keys)) (PArray.length m.(keys) - 1)%uint63 nil.

    #[local]
    Fixpoint find_any_to (f : key -> elt -> bool) (m : t) (count : nat) (i : int) : bool :=
      match count with
      | 0 => false
      | S count =>
          if f (PArray.get m.(keys) i) (PArray.get m.(values) i) then true
          else find_any_to f m count (i - 1)%uint63
      end.

    Definition find_any (f : key -> elt -> bool) (m : t) :=
      find_any_to f m (Z.to_nat $ Uint63_Fast.to_Z_pos $ PArray.length m.(keys)) (PArray.length m.(keys) - 1)%uint63.

    Definition copy (m : t) : t :=
      mk (PArray.copy m.(keys)) (PArray.copy m.(values)).

    Definition cardinal (m : t) : nat :=
      Z.to_nat $ Uint63_Fast.to_Z_pos $ PArray.length m.(keys).

    Lemma cardinal_1 : forall m, cardinal m = length (elements m).
    Proof.
      rewrite /cardinal/elements.
      intros.
      move L: (PArray.length (keys m)) => len.
      rewrite Uint63_Fast.to_Z_pos_rec_spec.
      move : (to_nat len) => n.
      have {1}-> : n = n + @length (key * elt) [] by done.
      move: (len - 1)%uint63 => i.
      move: [] => acc.
      elim: n N i acc => [|n IH] N i acc //.
      rewrite -IH //=.
    Qed.

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
