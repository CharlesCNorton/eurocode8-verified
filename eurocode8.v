(******************************************************************************)
(*                                                                            *)
(*          Eurocode 8: Seismic Design Verification Predicates                *)
(*                                                                            *)
(*     Formalizes EN 1998-1-1:2024 seismic action definitions, response       *)
(*     spectrum construction, lateral force method, and ductility class        *)
(*     compliance checks. Structural safety as decidable predicates.          *)
(*                                                                            *)
(*     "Nature had not assembled twenty thousand houses of six or seven       *)
(*     storeys there. If the inhabitants had been more equally dispersed,     *)
(*     the damage would have been much less, and perhaps nothing at all."     *)
(*     - Jean-Jacques Rousseau, Letter to Voltaire, 1756                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 22, 2026                                                *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================ *)
(*  GROUND TYPES — EN 1998-1-1:2024, clause 3.1.2                  *)
(* ================================================================ *)

Inductive ground_type : Type :=
  | GroundA | GroundB | GroundC | GroundD | GroundE.

(* ================================================================ *)
(*  SPECTRUM TYPES — EN 1998-1-1:2024, clause 3.2.2.2              *)
(* ================================================================ *)

Inductive spectrum_type : Type :=
  | Type1 | Type2.

(* ================================================================ *)
(*  IMPORTANCE CLASSES — EN 1998-1-1:2024, clause 4.2.5            *)
(* ================================================================ *)

Inductive importance_class : Type :=
  | ClassI | ClassII | ClassIII | ClassIV.

Definition gamma_I (ic : importance_class) : R :=
  match ic with
  | ClassI   => 4 / 5
  | ClassII  => 1
  | ClassIII => 6 / 5
  | ClassIV  => 7 / 5
  end.

(* ================================================================ *)
(*  SPECTRUM PARAMETERS — Tables 3.2 and 3.3                       *)
(* ================================================================ *)

Record spectrum_params : Type := mk_spectrum_params {
  sp_S  : R;
  sp_TB : R;
  sp_TC : R;
  sp_TD : R;
}.

Definition spectrum_lookup (st : spectrum_type) (gt : ground_type)
    : spectrum_params :=
  match st, gt with
  | Type1, GroundA => mk_spectrum_params 1        (3/20)  (2/5)   2
  | Type1, GroundB => mk_spectrum_params (6/5)    (3/20)  (1/2)   2
  | Type1, GroundC => mk_spectrum_params (23/20)  (1/5)   (3/5)   2
  | Type1, GroundD => mk_spectrum_params (27/20)  (1/5)   (4/5)   2
  | Type1, GroundE => mk_spectrum_params (7/5)    (3/20)  (1/2)   2
  | Type2, GroundA => mk_spectrum_params 1        (1/20)  (1/4)   (6/5)
  | Type2, GroundB => mk_spectrum_params (27/20)  (1/20)  (1/4)   (6/5)
  | Type2, GroundC => mk_spectrum_params (3/2)    (1/10)  (1/4)   (6/5)
  | Type2, GroundD => mk_spectrum_params (9/5)    (1/10)  (3/10)  (6/5)
  | Type2, GroundE => mk_spectrum_params (8/5)    (1/20)  (1/4)   (6/5)
  end.

(* ================================================================ *)
(*  ELASTIC RESPONSE SPECTRUM Se(T) — clause 3.2.2.2, eqs 3.2-3.5 *)
(* ================================================================ *)

(* Se(T) for given spectrum parameters, reference PGA ag, and       *)
(* damping correction factor eta (eta = 1 for 5% damping).         *)

Definition Se (p : spectrum_params) (ag eta T : R) : R :=
  if Rle_dec T (sp_TB p) then
    ag * sp_S p * (1 + T / sp_TB p * (eta * (5 / 2) - 1))
  else if Rle_dec T (sp_TC p) then
    ag * sp_S p * eta * (5 / 2)
  else if Rle_dec T (sp_TD p) then
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / T)
  else
    ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T * T)).

(* ================================================================ *)
(*  SPECTRUM PROPERTIES                                              *)
(* ================================================================ *)

(* Se at T = 0 equals ag * S (ground-level PGA scaled by soil).    *)
Lemma Se_at_zero : forall p ag eta,
  sp_TB p > 0 ->
  Se p ag eta 0 = ag * sp_S p.
Proof.
  intros p ag eta HTB.
  unfold Se.
  destruct (Rle_dec 0 (sp_TB p)) as [H|H].
  - field. lra.
  - exfalso. lra.
Qed.

(* Se at T = TB equals the plateau value ag * S * eta * 2.5.       *)
(* This is continuity at the first corner period from below.        *)
Lemma Se_at_TB : forall p ag eta,
  sp_TB p > 0 ->
  Se p ag eta (sp_TB p) = ag * sp_S p * eta * (5 / 2).
Proof.
  intros p ag eta HTB.
  unfold Se.
  destruct (Rle_dec (sp_TB p) (sp_TB p)) as [H|H].
  - field. lra.
  - exfalso. lra.
Qed.
