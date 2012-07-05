(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Raxioms Rbase QArith_base Qreals LegacyField.
Import LegacyRing_theory.

Section LegacyQField.

(** In the past, the field tactic was not able to deal with setoid datatypes,
    so translating from Q to R and applying field on reals was a workaround.
    See now Qfield for a direct field tactic on Q. *)

Ltac QField := apply eqR_Qeq; autorewrite with q2r_simpl; try field; auto.

(** Examples of use: *)

Let ex1 : forall x y z : Q, (x+y)*z == (x*z)+(y*z).
intros; QField.
Qed.

Let ex2 : forall x y : Q, ~ y==0 -> (x/y)*y == x.
intros; QField.
intro; apply H; apply eqR_Qeq.
rewrite H0; unfold Q2R; simpl; field; auto with real.
Qed.

End LegacyQField.
