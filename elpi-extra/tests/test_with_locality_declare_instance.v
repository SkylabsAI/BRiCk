(*
 * Copyright (c) 2024 BedRock Systems Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1-or-later
 *
 * The following code is derived from code original to the
 * Coq-elpi project. That original code is used according to the following license.
 *
 * SPDX-License-Identifier: LGPL-2.1-or-later
 *
 * Original Coq-Elpi License:
 * https://github.com/LPCIC/coq-elpi/blob/1e13238bcabdff52bef47f8867e221ce12d0c92b/LICENSE
 *
 * Derived from
 * https://github.com/LPCIC/coq-elpi/blob/1e13238bcabdff52bef47f8867e221ce12d0c92b/tests/test_API_TC_CS.v,
 * but using [coq.locality.with!].
 *)

Require Import elpi.elpi.
Elpi Command TC.

Require Export bedrock.elpi.extra.extra.
#[phase="both"] Elpi Accumulate TC Db extra.Command.

Require Import Classes.RelationClasses.

Axiom T : Type.
Axiom R : T -> T -> Prop.
Axiom Rr : forall x : T, R x x.

Definition myi : Reflexive R := Rr.

Fail Example ex : Reflexive R := _.

Module TCLocal.
  Elpi Query lp:{{ coq.locate "myi" GR,
    coq.locality.with! coq.locality.l (coq.TC.declare-instance GR 10). }}.
  Succeed Example ex : Reflexive R := _.
End TCLocal.

Fail Example ex : Reflexive R := _.

Module TCExport.
  Fail Example ex : Reflexive R := _.
  Module Mod.
    Elpi Query lp:{{ coq.locate "myi" GR, coq.locality.with! coq.locality.e (coq.TC.declare-instance GR 10). }}.
  End Mod.
  Fail Example ex : Reflexive R := _.
  Import Mod.
  Check (_ : Reflexive R).
  Succeed Example ex : Reflexive R := _.
End TCExport.

Fail Example ex : Reflexive R := _.

Module TCGlobal.
  Elpi Query lp:{{ coq.locate "myi" GR, coq.locality.with! coq.locality.g (coq.TC.declare-instance GR 10). }}.
End TCGlobal.
Succeed Example ex : Reflexive R := _.
