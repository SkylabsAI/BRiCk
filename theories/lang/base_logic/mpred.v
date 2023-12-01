(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
This file defines the core [bi] (called [mpred]) that we use for all of our logics.
It is a [bi] parameterized by:
1. a thread information (via [monPred]) that allows distinguishing between
  different implicit contexts, and
2. a CMRA structure in the style of Iris, i.e. [gFunctors], that allows for
  higher-order ghost state.

The construction also bakes in the common pattern of allowing to store global
ghost names directly in the logic rather than needing to pass them separately.
*)

From iris.base_logic.lib Require Import own cancelable_invariants.
Require Import iris.bi.monpred.

From bedrock.prelude Require Import base.
From bedrock.lang Require Import bi.prelude bi.entailsN.
From bedrock.lang.cpp.logic Require Import upred_entailsN monpred_entailsN.
Import ChargeNotation.

Module LOGIC.
  (** Types of Cmras that a logic requires

  An instance of [GpreS] packages the _types_ of the cmras that a logic's
  [Σ : gFunctors] should have. By default, we require that any logic's [Σ] should
  have invariants, i.e. [invGS Σ] and [cinvG Σ].

  For example, a machine logic would have an instance [machineGpreS : GpreS]
  as follows.
<<
  Record machine_preGS {Σ : gFunctors} {thread_info : biIndex} : Type := {
    machine_pbyte_heapGS : inG Σ (gmapR ...)
  ; ... (* more Cmras *)
  ; machine_has_inv : invGS Σ
  ; machine_has_cinv : cinvG Σ
  }.
  #[global] Arguments machine_preGS : clear implicits.

  Definition machineGpreS (Σ : gFunctors) (thread_info : biIndex) : GpreS Σ thread_info := {|
    preGS := machine_preGS Σ thread_info
  ; preGS_has_inv := machine_has_inv
  ; preGS_has_cinv := machine_has_cinv
  |}.
>>

  The instance for a NOVA logic [novaGpreS : GpreS] would be as follows.
<<
  Record nova_preGS {Σ : gFunctors} {thread_info : biIndex} : Type := {
    nova_has_machine : machine_preGS Σ thread_info
  ; ... (* more Cmras *)
  }.
  #[global] Arguments nova_preGS : clear implicits.

  Definition novaGpreS (Σ : gFunctors) (thread_info : biIndex) : GpreS Σ thread_info := {|
    preGS := nova_preGS Σ thread_info
  ; preGS_has_inv := machine_has_inv ∘ nova_has_machine
  ; preGS_has_cinv := machine_has_cinv ∘ nova_has_machine
  |}.
>>

  The instance for a C++ logic for a C++ abstract machine atop NOVA would build
  on [novaGpreS] similarly.
  For a C++ abstract machine that is not built on top of NOVA, its logic would
  build directly on [machineGpreS].
  *)
  Class GpreS {Σ : gFunctors} {thread_info : biIndex} : Type := {
    preGS : Type
  ; preGS_has_inv : preGS -> invGS Σ
  ; preGS_has_cinv : preGS -> cinvG Σ
  } .
  Existing Class preGS.
  (* Not making preGS_has_inv/cinv instances, we use logic_has_inv/cinv below instead. *)
  #[global] Arguments GpreS : clear implicits.
  #[global] Hint Mode GpreS - - : typeclass_instances.

  (** Types of cmras and global ghost names that a logic has

  An instance of [GS] packages not only the Cmras, but also the type [GS_ghost]
  of all global ghost names that a logic relies on.
<<
  Record machine_ghost : Type := {
    machine_pbyte_heap_name : gname
  ; ... (* more global ghost name types for machine *)
  }.

  Definition machineGS Σ thread_info : GS Σ thread_info := {|
    GS_pre := machineGpreS Σ thread_info
  ; GS_ghost := machine_ghost
  |}.

  Record nova_ghost : Type := {
    nova_ghost_has_machine : machine_ghost (* nova_ghost includes machine_ghost *)
  ; ... (* more global ghost name types for nova *)
  }.

  Definition novaGS Σ thread_info : GS Σ thread_info := {|
    GS_pre := novaGpreS Σ thread_info
  ; GS_ghost := nova_ghost
  |}.
>>
  *)
  Class GS {Σ : gFunctors} {thread_info : biIndex} : Type := {
    GS_pre : GpreS Σ thread_info
  ; GS_ghost : Type
  }.
  #[global] Arguments GS : clear implicits.
  #[global] Hint Mode GS - - : typeclass_instances.

  (** An inclusion relation between ghost types

  [subGS gtype1 gtype2] (tentative notation gtype1 ⊆ gtype2) means that
  - [subGS_pre]: the cmras of [gtype2] include the cmras of [gtype1]
  - [subGS_ghost]: the ghost names of [gtype2] include the ghost names of [gtype1]

  This relation captures the fact that one logic is built on top of the other,
  for example, machineGS ⊆ novaGS ⊆ cppGS means that the C++ logic is built on
  top of the NOVA logic, which in turn is built on the machine logic.
  *)
  Class subGS {Σ : gFunctors} {thread_info : biIndex}
      (gtype1 gtype2 : GS Σ thread_info) := {
    subGS_pre : @preGS Σ thread_info gtype2.(GS_pre) -> @preGS Σ thread_info gtype1.(GS_pre)
  ; subGS_ghost : gtype2.(GS_ghost) -> gtype1.(GS_ghost)
  }.
  #[global] Hint Mode subGS - - - - : typeclass_instances.

  (** An instance of a logic

  The instance packages
  - [_ghost_type : GS _Σ thread_info]: the types of cmras and global ghost names
    that the logic needs
  - a gFunctors _Σ that satisfies the requirement of [_ghost_type], i.e. [_has_G]
    says that _Σ includes the cmras in [_ghost_type.(GS_pre)]
  - a concrete instance of ghost names [_ghost]

  A logic should have only one such instance, for example there should be only
  one instance [machine_logic] and one instance [nova_logic].
  However, we may have multiple C++ logic instances [cpp_logic], each for one
  C++ abstract machine instance. Each [cpp_logic] would use the same ghost type
  [cppGS] (GS stands for Ghost Singleton), but would have different concrete
  ghost names [_ghost].
  *)
  Class logic {thread_info : biIndex} : Type :=
  { _Σ          : gFunctors
  ; _ghost_type : GS _Σ thread_info
  ; _ghost      : _ghost_type.(GS_ghost)
  ; #[global] _has_G :: @preGS _Σ thread_info _ghost_type.(GS_pre)
  }.
  #[global] Arguments logic : clear implicits.
  #[global] Hint Mode logic - : typeclass_instances.

  #[global] Instance logic_has_inv `{!logic thread_info} : invGS _Σ
    := preGS_has_inv _has_G.
  #[global] Instance logic_has_cinv `{!logic thread_info} : cinvG _Σ
    := preGS_has_cinv _has_G.
  #[global] Hint Opaque logic_has_inv logic_has_cinv : typeclass_instances br_opacity.

  (** A logic instance is at least some logic

  The logic instance [Σ] includes [gtype], so it is at least the logic of [gtype].
  Consequently, any predicates for a logic that only depends on [gtype] can be
  used in the logic [Σ], that is, they can be embedded into a larger logic.

  To define a predicate that only depends on a concrete GS, we would do the
  following:
<<
  Section pbyte_at.
    (* pbyte_at only need machine ghosts *)
    Context `{Σ : logic thread_info} `{!HasGS Σ thread_info (machineGS Σ thread_info)}.

    Definition pbyte_at ... := ...
  End pbyte_at.
>>
  Then, with an instance that [subGS (machineGS Σ thread_info) (novaGS Σ thread_info)],
  in a context with the nova logic, [pbyte_at] should be usable.
<<
  Section nova_logic.
    Context `{Σ : logic thread_info} `{!HasGS Σ thread_info (novaGS Σ thread_info)}.

    Definitiion vbyte_at ... :=
      page_mapping ... **
      pbyte_at ...
      .
  End nova_logic.
>>
  *)
  Class HasGS `{Σ : logic thread_info} (gtype : GS _Σ thread_info) := {
    has_subGS : subGS gtype _ghost_type
  }.
  #[global] Hint Mode HasGS - - - : typeclass_instances.

End LOGIC.
#[global] Coercion LOGIC._Σ : LOGIC.logic >-> gFunctors.
#[global] Hint Opaque LOGIC._Σ : typeclass_instances br_opacity.
#[global] Opaque LOGIC._Σ.
Export LOGIC(_Σ,_ghost).

Section mpred.
  Context `{Σ : !LOGIC.logic thread_info}.

  (* TODO: seal *)
  Definition mpredI : bi := monPredI thread_info (iPropI Σ).
  Definition mpred := bi_car mpredI.

  (* TODO: don't make this a Canonical Structure as it depends on LOGIC.logic *)
  Canonical Structure mpredO : ofe
    := Ofe mpred (ofe_mixin (monPredO thread_info (iPropI Σ))).

  (* We name this, for manual use later when importing [linearity]. *)
  Lemma mpred_BiAffine : BiAffine mpred.
  Proof. apply _. Qed.

  (* HACK: this is to prevent IPM from simplifying [mpred] into [monPred].
  Sealing mpred is better *)
  #[global] Instance : BiBUpd mpredI | 0 := monPred_bi_bupd _ _.
  #[global] Instance : BiFUpd mpredI | 0 := monPred_bi_fupd _ _.
  #[global] Instance : BiEntailsN mpredI | 0 := monPred_bi_entailsN.

End mpred.

Bind Scope bi_scope with mpred.

(**
To implement higher-order ghost state mentioning [mpred], we
presuppose [mpred ≈ I -mon> iProp] and use the discrete OFE [I -d>
iProp Σ] rather than [monPredO]. We cannot use [monPredO] because Iris
lacks a functor [monPredOF].
*)
Definition later_mpredO (Σ : gFunctors) (thread_info : biIndex) : ofe :=
  laterO (thread_info -d> iPropI Σ).
Definition later_mpredOF (thread_info : biIndex) : oFunctor :=
  laterOF (thread_info -d> idOF).
Definition later_mpred `{Σ : !LOGIC.logic thread_info} (P : mpred) :
    later (thread_info -d> iPropI Σ) :=
  Next (monPred_at P).

Section later_mpred.
  Context `{Σ : !LOGIC.logic thread_info}.

  #[global] Instance later_mpred_contractive : Contractive later_mpred.
  Proof.
    move => n ?? HP. apply: Next_contractive.
    dist_later_intro. destruct n as [|n]; [lia | by destruct HP].
  Qed.
  #[global] Instance later_mpred_ne : NonExpansive later_mpred.
  Proof. exact: contractive_ne. Qed.
  #[global] Instance later_mpred_proper : Proper (equiv ==> equiv) later_mpred.
  Proof. exact: ne_proper. Qed.

  Lemma equivI_later_mpred P Q :
    later_mpred P ≡ later_mpred Q -|-@{mpredI} |> (P ≡ Q).
  Proof.
    rewrite /later_mpred later_equivI.
    by rewrite discrete_fun_equivI monPred_equivI.
  Qed.
End later_mpred.
#[global] Hint Opaque later_mpred : typeclass_instances.
