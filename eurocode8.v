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

Require Import Reals Lra List.
Import ListNotations.
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

(* Se at T = TC equals the plateau value (branch 2 evaluation).       *)
Lemma Se_at_TC : forall p ag eta,
  sp_TB p < sp_TC p ->
  Se p ag eta (sp_TC p) = ag * sp_S p * eta * (5 / 2).
Proof.
  intros p ag eta H.
  unfold Se.
  destruct (Rle_dec (sp_TC p) (sp_TB p)) as [H1|H1].
  - exfalso. lra.
  - destruct (Rle_dec (sp_TC p) (sp_TC p)) as [H2|H2].
    + reflexivity.
    + exfalso. lra.
Qed.

(* Continuity at TC: Se(TC) agrees with the descending-branch formula. *)
Lemma Se_continuous_at_TC : forall p ag eta,
  sp_TB p < sp_TC p ->
  sp_TC p > 0 ->
  Se p ag eta (sp_TC p) =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / sp_TC p).
Proof.
  intros p ag eta HTB HTC.
  unfold Se.
  destruct (Rle_dec (sp_TC p) (sp_TB p)) as [H1|H1].
  - exfalso. lra.
  - destruct (Rle_dec (sp_TC p) (sp_TC p)) as [H2|H2].
    + field. lra.
    + exfalso. lra.
Qed.

(* Se at T = TD equals the descending-branch value ag*S*eta*2.5*TC/TD. *)
Lemma Se_at_TD : forall p ag eta,
  sp_TB p < sp_TD p ->
  sp_TC p < sp_TD p ->
  Se p ag eta (sp_TD p) =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / sp_TD p).
Proof.
  intros p ag eta HTB HTC.
  unfold Se.
  destruct (Rle_dec (sp_TD p) (sp_TB p)) as [H1|H1].
  - exfalso. lra.
  - destruct (Rle_dec (sp_TD p) (sp_TC p)) as [H2|H2].
    + exfalso. lra.
    + destruct (Rle_dec (sp_TD p) (sp_TD p)) as [H3|H3].
      * reflexivity.
      * exfalso. lra.
Qed.

(* Continuity at TD: Se(TD) agrees with the 1/T^2-branch formula.     *)
Lemma Se_continuous_at_TD : forall p ag eta,
  sp_TB p < sp_TD p ->
  sp_TC p < sp_TD p ->
  sp_TD p > 0 ->
  Se p ag eta (sp_TD p) =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (sp_TD p * sp_TD p)).
Proof.
  intros p ag eta HTB HTC HTD.
  unfold Se.
  destruct (Rle_dec (sp_TD p) (sp_TB p)) as [H1|H1].
  - exfalso. lra.
  - destruct (Rle_dec (sp_TD p) (sp_TC p)) as [H2|H2].
    + exfalso. lra.
    + destruct (Rle_dec (sp_TD p) (sp_TD p)) as [H3|H3].
      * field. lra.
      * exfalso. lra.
Qed.

(* ================================================================ *)
(*  MONOTONICITY PROPERTIES — item 5                                *)
(* ================================================================ *)

(* Se is strictly increasing on [0, TB].                             *)
Lemma Se_increasing : forall p ag eta T1 T2,
  ag > 0 -> sp_S p > 0 -> eta * (5 / 2) > 1 -> sp_TB p > 0 ->
  0 <= T1 -> T1 < T2 -> T2 <= sp_TB p ->
  Se p ag eta T1 < Se p ag eta T2.
Proof.
  intros p ag eta T1 T2 Hag HS Heta HTB HT1 HT12 HT2.
  unfold Se.
  destruct (Rle_dec T1 (sp_TB p)) as [H1|H1]; [|lra].
  destruct (Rle_dec T2 (sp_TB p)) as [H2|H2]; [|lra].
  apply Rmult_lt_compat_l.
  { apply Rmult_lt_0_compat; lra. }
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_r; [lra|].
  unfold Rdiv.
  apply Rmult_lt_compat_r.
  { apply Rinv_0_lt_compat. lra. }
  lra.
Qed.

(* Se is constant (plateau) on (TB, TC].                             *)
Lemma Se_plateau : forall p ag eta T,
  sp_TB p < T -> T <= sp_TC p ->
  Se p ag eta T = ag * sp_S p * eta * (5 / 2).
Proof.
  intros p ag eta T HTB HTC.
  unfold Se.
  destruct (Rle_dec T (sp_TB p)); [lra|].
  destruct (Rle_dec T (sp_TC p)); [reflexivity|lra].
Qed.

(* Se is strictly decreasing on (TC, TD].                            *)
Lemma Se_decreasing_TC_TD : forall p ag eta T1 T2,
  ag > 0 -> sp_S p > 0 -> eta > 0 ->
  sp_TC p > 0 -> sp_TB p < sp_TC p ->
  sp_TC p < T1 -> T1 < T2 -> T2 <= sp_TD p ->
  Se p ag eta T2 < Se p ag eta T1.
Proof.
  intros p ag eta T1 T2 Hag HS Heta HTC HTB HT1 HT12 HT2.
  assert (HSeT1: Se p ag eta T1 =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / T1)).
  { unfold Se.
    destruct (Rle_dec T1 (sp_TB p)); [lra|].
    destruct (Rle_dec T1 (sp_TC p)); [lra|].
    destruct (Rle_dec T1 (sp_TD p)); [reflexivity|lra]. }
  assert (HSeT2: Se p ag eta T2 =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / T2)).
  { unfold Se.
    destruct (Rle_dec T2 (sp_TB p)); [lra|].
    destruct (Rle_dec T2 (sp_TC p)); [lra|].
    destruct (Rle_dec T2 (sp_TD p)); [reflexivity|lra]. }
  rewrite HSeT1, HSeT2.
  apply Rmult_lt_compat_l.
  { apply Rmult_lt_0_compat; [|lra].
    apply Rmult_lt_0_compat; [|lra].
    apply Rmult_lt_0_compat; lra. }
  unfold Rdiv.
  apply Rmult_lt_compat_l; [lra|].
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; lra.
  - lra.
Qed.

(* Se is strictly decreasing on (TD, +inf).                          *)
Lemma Se_decreasing_TD_inf : forall p ag eta T1 T2,
  ag > 0 -> sp_S p > 0 -> eta > 0 ->
  sp_TC p > 0 -> sp_TD p > 0 ->
  sp_TB p < sp_TC p -> sp_TC p < sp_TD p ->
  sp_TD p < T1 -> T1 < T2 ->
  Se p ag eta T2 < Se p ag eta T1.
Proof.
  intros p ag eta T1 T2 Hag HS Heta HTC HTD HTB HTC_TD HT1 HT12.
  assert (HSeT1: Se p ag eta T1 =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T1 * T1))).
  { unfold Se.
    destruct (Rle_dec T1 (sp_TB p)); [lra|].
    destruct (Rle_dec T1 (sp_TC p)); [lra|].
    destruct (Rle_dec T1 (sp_TD p)); [lra|].
    reflexivity. }
  assert (HSeT2: Se p ag eta T2 =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T2 * T2))).
  { unfold Se.
    destruct (Rle_dec T2 (sp_TB p)); [lra|].
    destruct (Rle_dec T2 (sp_TC p)); [lra|].
    destruct (Rle_dec T2 (sp_TD p)); [lra|].
    reflexivity. }
  rewrite HSeT1, HSeT2.
  apply Rmult_lt_compat_l.
  { apply Rmult_lt_0_compat; [|lra].
    apply Rmult_lt_0_compat; [|lra].
    apply Rmult_lt_0_compat; lra. }
  unfold Rdiv.
  apply Rmult_lt_compat_l.
  { apply Rmult_lt_0_compat; lra. }
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; lra.
  - apply Rlt_trans with (T2 * T1).
    + apply Rmult_lt_compat_r; lra.
    + apply Rmult_lt_compat_l; lra.
Qed.

(* ================================================================ *)
(*  DUCTILITY CLASSES — EN 1998-1-1:2024, clause 5.2.1              *)
(* ================================================================ *)

Inductive ductility_class : Type :=
  | DCL | DCM | DCH.

(* ================================================================ *)
(*  STRUCTURAL SYSTEM TYPES — EN 1998-1-1:2024, Table 5.1           *)
(* ================================================================ *)

Inductive structural_system : Type :=
  | FrameSystem
  | DualFrameEquiv
  | DualWallEquiv
  | DuctileWallSystem
  | InvertedPendulum
  | TorsionallyFlexible.

(* ================================================================ *)
(*  BEHAVIOR FACTOR q0 — EN 1998-1-1:2024, Table 5.1                *)
(* ================================================================ *)

(* Basic behavior factor q0.  For system types where q0 depends on   *)
(* the overstrength ratio alpha_u/alpha_1, the parameter au_a1 is    *)
(* used; otherwise it is ignored.                                    *)

Definition q0 (dc : ductility_class) (ss : structural_system)
    (au_a1 : R) : R :=
  match dc, ss with
  | DCL, _                     => 3 / 2
  | DCM, FrameSystem           => 3 * au_a1
  | DCM, DualFrameEquiv        => 3 * au_a1
  | DCM, DualWallEquiv         => 3
  | DCM, DuctileWallSystem     => 3
  | DCM, InvertedPendulum      => 3 / 2
  | DCM, TorsionallyFlexible   => 2
  | DCH, FrameSystem           => 9 / 2 * au_a1
  | DCH, DualFrameEquiv        => 9 / 2 * au_a1
  | DCH, DualWallEquiv         => 4 * au_a1
  | DCH, DuctileWallSystem     => 4 * au_a1
  | DCH, InvertedPendulum      => 2
  | DCH, TorsionallyFlexible   => 3
  end.

(* ================================================================ *)
(*  DESIGN SPECTRUM Sd(T) — EN 1998-1-1:2024, clause 3.2.2.5        *)
(* ================================================================ *)

(* Lower bound factor beta = 0.2 per clause 3.2.2.5(4)P.            *)
Definition beta : R := 1 / 5.

(* Design spectrum: Sd(T) = max(Se(T)/q, beta*ag).                  *)
Definition Sd (p : spectrum_params) (ag eta : R) (q : R) (T : R) : R :=
  Rmax (Se p ag eta T / q) (beta * ag).

(* Sd(T) >= beta * ag for all T — the floor is always active.       *)
Lemma Sd_floor : forall p ag eta q T,
  Sd p ag eta q T >= beta * ag.
Proof.
  intros. unfold Sd. apply Rle_ge. apply Rmax_r.
Qed.

(* Sd(T) <= Se(T) when q >= 1 and beta*ag <= Se(T).                 *)
Lemma Sd_le_Se : forall p ag eta q T,
  q >= 1 -> Se p ag eta T >= 0 -> beta * ag <= Se p ag eta T ->
  Sd p ag eta q T <= Se p ag eta T.
Proof.
  intros p ag eta q T Hq Hse Hbeta.
  unfold Sd.
  apply Rmax_lub; [|lra].
  unfold Rdiv.
  rewrite <- (Rmult_1_r (Se p ag eta T)) at 2.
  apply Rmult_le_compat_l; [lra|].
  apply (Rmult_le_reg_l q); [lra|].
  rewrite Rinv_r; [|lra]. rewrite Rmult_1_r. lra.
Qed.

(* ================================================================ *)
(*  LATERAL FORCE METHOD — EN 1998-1-1:2024, clause 4.3.3.2         *)
(* ================================================================ *)

(* Applicability: T1 <= 4*TC and the building is regular in          *)
(* elevation.                                                        *)
Definition lateral_force_applicable (T1 : R) (p : spectrum_params)
    (elevation_regular : Prop) : Prop :=
  T1 <= 4 * sp_TC p /\ elevation_regular.

(* ================================================================ *)
(*  BASE SHEAR — EN 1998-1-1:2024, clause 4.3.3.2.2                 *)
(* ================================================================ *)

(* Correction factor lambda: 0.85 if T1 <= 2*TC and >= 3 storeys,   *)
(* 1.0 otherwise.                                                   *)
Definition lambda (T1 : R) (p : spectrum_params) (n_storeys : nat) : R :=
  if Rle_dec T1 (2 * sp_TC p) then
    if Nat.leb 3 n_storeys then 17 / 20 else 1
  else
    1.

(* Base shear force Fb.                                              *)
Definition Fb (sd_T1 m : R) (lam : R) : R := sd_T1 * m * lam.

(* ================================================================ *)
(*  STOREY FORCE DISTRIBUTION — clause 4.3.3.2.3                    *)
(* ================================================================ *)

(* A storey is a (height, mass) pair.                                *)
Record storey : Type := mk_storey {
  st_z : R;   (* height above base *)
  st_m : R;   (* seismic mass *)
}.

(* Weighted sum Σ(zj * mj).                                         *)
Fixpoint sum_zm (storeys : list storey) : R :=
  match storeys with
  | nil => 0
  | s :: rest => st_z s * st_m s + sum_zm rest
  end.

(* Storey force Fi = Fb * (zi * mi) / Σ(zj * mj).                   *)
Definition Fi (fb : R) (s : storey) (szm : R) : R :=
  fb * (st_z s * st_m s) / szm.

(* Compute all storey forces for a building.                         *)
Definition storey_forces (fb : R) (storeys : list storey) : list R :=
  let szm := sum_zm storeys in
  map (fun s => Fi fb s szm) storeys.

(* Sum of a list of reals.                                           *)
Fixpoint sum_R (l : list R) : R :=
  match l with
  | nil => 0
  | x :: rest => x + sum_R rest
  end.

(* Key helper: sum of (fb * zi*mi / szm) = fb * (sum zi*mi) / szm.  *)
Lemma sum_Fi_factor : forall fb storeys szm,
  sum_R (map (fun s => Fi fb s szm) storeys) =
  fb * sum_zm storeys / szm.
Proof.
  intros fb storeys szm.
  induction storeys as [|s rest IH]; simpl.
  - unfold Fi, Rdiv. ring.
  - unfold Fi, Rdiv in *. rewrite IH. ring.
Qed.

(* ΣFi = Fb when Σ(zj*mj) > 0.                                     *)
Lemma sum_Fi_eq_Fb : forall fb storeys,
  sum_zm storeys > 0 ->
  sum_R (storey_forces fb storeys) = fb.
Proof.
  intros fb storeys Hszm.
  unfold storey_forces.
  rewrite sum_Fi_factor.
  unfold Rdiv. rewrite Rmult_assoc.
  rewrite Rinv_r; [|lra]. ring.
Qed.

(* Fi > 0 for storeys with positive height, mass, and base shear.   *)
Lemma Fi_pos : forall fb s szm,
  fb > 0 -> st_z s > 0 -> st_m s > 0 -> szm > 0 ->
  Fi fb s szm > 0.
Proof.
  intros fb s szm Hfb Hz Hm Hszm.
  unfold Fi, Rdiv.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [|apply Rmult_lt_0_compat]; lra.
  - apply Rinv_0_lt_compat. lra.
Qed.

(* ================================================================ *)
(*  DISPLACEMENT AMPLIFICATION — clause 4.3.4                       *)
(* ================================================================ *)

(* ds = q * de, where de is the elastic displacement from analysis.  *)
Definition ds (q de : R) : R := q * de.

(* ================================================================ *)
(*  DRIFT LIMITS — EN 1998-1-1:2024, clause 4.4.3.2                 *)
(* ================================================================ *)

(* Non-structural element attachment category.                       *)
Inductive ns_category : Type :=
  | NS_Brittle       (* brittle non-structural elements *)
  | NS_Ductile       (* ductile non-structural elements *)
  | NS_None.         (* no non-structural elements *)

(* Drift limit as fraction of storey height.                         *)
Definition drift_limit (cat : ns_category) : R :=
  match cat with
  | NS_Brittle => 1 / 200    (* 0.005 h *)
  | NS_Ductile => 15 / 2000  (* 0.0075 h *)
  | NS_None    => 1 / 100    (* 0.010 h *)
  end.

(* Reduction factor nu for lower return period.                      *)
Definition nu : R := 1 / 2.

(* Drift check: dr * nu <= drift_limit * h.                          *)
Definition drift_ok (cat : ns_category) (dr h : R) : Prop :=
  dr * nu <= drift_limit cat * h.

(* Drift check is decidable.                                         *)
Lemma drift_ok_dec : forall cat dr h,
  { drift_ok cat dr h } + { ~ drift_ok cat dr h }.
Proof.
  intros. unfold drift_ok.
  apply Rle_dec.
Qed.

(* Ductile drift limit is strictly more permissive than brittle.     *)
Lemma drift_ductile_more_permissive : forall dr h,
  h > 0 -> drift_ok NS_Brittle dr h -> drift_ok NS_Ductile dr h.
Proof.
  intros dr h Hh Hb. unfold drift_ok in *.
  simpl in *. lra.
Qed.

(* ================================================================ *)
(*  P-DELTA EFFECTS — EN 1998-1-1:2024, clause 4.4.2.2              *)
(* ================================================================ *)

(* Interstorey drift sensitivity coefficient.                        *)
(* theta = Ptot * dr / (Vtot * h)                                   *)
Definition theta (Ptot dr Vtot h : R) : R :=
  Ptot * dr / (Vtot * h).

(* P-Delta regime classification.                                    *)
Inductive pdelta_regime : Type :=
  | PD_Negligible    (* theta <= 0.10: no amplification needed *)
  | PD_Approximate   (* 0.10 < theta <= 0.20: multiply by 1/(1-theta) *)
  | PD_Detailed      (* 0.20 < theta <= 0.30: explicit 2nd-order *)
  | PD_Inadmissible. (* theta > 0.30: not permitted *)

Definition classify_pdelta (th : R) : pdelta_regime :=
  if Rle_dec th (1/10) then PD_Negligible
  else if Rle_dec th (1/5) then PD_Approximate
  else if Rle_dec th (3/10) then PD_Detailed
  else PD_Inadmissible.

(* Amplification factor for P-Delta effects.                         *)
Definition pdelta_amplification (th : R) : R := 1 / (1 - th).

(* 1/(1-theta) is in [1, 1.25] when theta is in (0.10, 0.20].       *)
Lemma pdelta_amp_lower : forall th,
  1/10 < th -> th <= 1/5 ->
  pdelta_amplification th >= 1.
Proof.
  intros th Hlo Hhi. unfold pdelta_amplification.
  unfold Rdiv. rewrite Rmult_1_l.
  apply Rle_ge. rewrite <- Rinv_1 at 1.
  apply Rinv_le_contravar; lra.
Qed.

Lemma pdelta_amp_upper : forall th,
  1/10 < th -> th <= 1/5 ->
  pdelta_amplification th <= 5/4.
Proof.
  intros th Hlo Hhi. unfold pdelta_amplification.
  assert (Hpos: 0 < 1 - th) by lra.
  cut (4 <= 5 * (1 - th)); [intro Hcut|lra].
  unfold Rdiv. rewrite Rmult_1_l.
  apply (Rmult_le_reg_l (1 - th)); [lra|].
  rewrite Rinv_r; [|lra].
  apply (Rmult_le_reg_l 4); [lra|].
  rewrite Rmult_1_r.
  replace (4 * ((1 - th) * (5 * / 4))) with (5 * (1 - th)) by (field; lra).
  lra.
Qed.

(* theta > 0.30 implies amplification > 10/7 ≈ 1.43.                *)
Lemma pdelta_amp_inadmissible : forall th,
  3/10 < th -> th < 1 ->
  pdelta_amplification th > 10/7.
Proof.
  intros th Hlo Hhi. unfold pdelta_amplification.
  assert (Hpos: 0 < 1 - th) by lra.
  cut (7 * (1 - th) < 10); [intro Hcut|lra].
  unfold Rdiv. rewrite Rmult_1_l.
  apply (Rmult_lt_reg_l (1 - th)); [lra|].
  rewrite Rinv_r; [|lra].
  apply (Rmult_lt_reg_l 7); [lra|].
  rewrite Rmult_1_r.
  replace (7 * ((1 - th) * (10 * / 7))) with (10 * (1 - th)) by (field; lra).
  lra.
Qed.

(* ================================================================ *)
(*  REGULARITY — EN 1998-1-1:2024, clause 4.2.3                     *)
(* ================================================================ *)

(* Plan regularity: compactness, eccentricity <= 0.30*r, torsional   *)
(* radius >= ls.  Parameters: eccentricity e0, torsional radius r,   *)
(* radius of gyration ls.                                            *)
Definition plan_regular (e0x e0y rx ry ls : R) : Prop :=
  e0x <= 3/10 * rx /\
  e0y <= 3/10 * ry /\
  rx >= ls /\
  ry >= ls.

(* Elevation regularity: mass ratio <= 150%, stiffness continuity,   *)
(* no abrupt setbacks.  Encodes clause 4.2.3.3 criteria.            *)
(* Parameters: per-storey mass and stiffness as lists.               *)

(* All adjacent pairs satisfy a predicate.                           *)
Fixpoint all_adjacent {A : Type} (P : A -> A -> Prop)
    (l : list A) : Prop :=
  match l with
  | nil => True
  | _ :: nil => True
  | x :: ((y :: _) as rest) => P x y /\ all_adjacent P rest
  end.

(* Mass ratio between adjacent storeys <= 150%.                      *)
Definition mass_ratio_ok (m1 m2 : R) : Prop :=
  m2 <= 3/2 * m1 /\ m1 <= 3/2 * m2.

(* Stiffness does not decrease abruptly (within 30% of storey above). *)
Definition stiffness_continuity (k_below k_above : R) : Prop :=
  k_below >= 7/10 * k_above.

Definition elevation_regular (masses stiffnesses : list R) : Prop :=
  all_adjacent mass_ratio_ok masses /\
  all_adjacent stiffness_continuity stiffnesses.

(* Plan-regular and elevation-regular implies lateral force method    *)
(* is applicable (given the period condition T1 <= 4*TC).            *)
Lemma regularity_implies_lfm : forall T1 p e0x e0y rx ry ls masses stiffs,
  plan_regular e0x e0y rx ry ls ->
  elevation_regular masses stiffs ->
  T1 <= 4 * sp_TC p ->
  lateral_force_applicable T1 p (elevation_regular masses stiffs).
Proof.
  intros. unfold lateral_force_applicable. split; assumption.
Qed.

(* ================================================================ *)
(*  FULL COMPLIANCE PREDICATE — composing all checks                *)
(* ================================================================ *)

Record building : Type := mk_building {
  bld_storeys    : list storey;
  bld_masses     : list R;
  bld_stiffnesses: list R;
  bld_T1         : R;       (* fundamental period *)
  bld_n_storeys  : nat;
  bld_e0x        : R;       (* eccentricity x *)
  bld_e0y        : R;       (* eccentricity y *)
  bld_rx         : R;       (* torsional radius x *)
  bld_ry         : R;       (* torsional radius y *)
  bld_ls         : R;       (* radius of gyration *)
}.

Record seismic_params : Type := mk_seismic_params {
  spar_sp     : spectrum_params;
  spar_ag     : R;
  spar_eta    : R;
  spar_q      : R;
  spar_ns_cat : ns_category;
}.

(* Per-storey verification data for drift and P-Delta checks.       *)
Record storey_data : Type := mk_storey_data {
  sd_dr    : R;   (* design interstorey drift *)
  sd_h     : R;   (* storey height *)
  sd_theta : R;   (* P-delta coefficient for this storey *)
}.

Fixpoint all_drifts_ok (cat : ns_category)
    (sds : list storey_data) : Prop :=
  match sds with
  | nil => True
  | sd :: rest =>
      drift_ok cat (sd_dr sd) (sd_h sd) /\ all_drifts_ok cat rest
  end.

Fixpoint all_pdelta_ok (sds : list storey_data) : Prop :=
  match sds with
  | nil => True
  | sd :: rest => sd_theta sd <= 3/10 /\ all_pdelta_ok rest
  end.

Definition ec8_compliant (b : building) (sp : seismic_params)
    (sds : list storey_data) : Prop :=
  plan_regular (bld_e0x b) (bld_e0y b) (bld_rx b) (bld_ry b) (bld_ls b) /\
  elevation_regular (bld_masses b) (bld_stiffnesses b) /\
  bld_T1 b <= 4 * sp_TC (spar_sp sp) /\
  all_drifts_ok (spar_ns_cat sp) sds /\
  all_pdelta_ok sds.

(* ================================================================ *)
(*  DECIDABILITY — item 28                                           *)
(* ================================================================ *)

Lemma plan_regular_dec : forall e0x e0y rx ry ls,
  { plan_regular e0x e0y rx ry ls } + { ~ plan_regular e0x e0y rx ry ls }.
Proof.
  intros. unfold plan_regular.
  destruct (Rle_dec e0x (3/10 * rx));
  destruct (Rle_dec e0y (3/10 * ry));
  destruct (Rge_dec rx ls);
  destruct (Rge_dec ry ls);
  try (left; tauto); right; tauto.
Qed.

Lemma all_drifts_ok_dec : forall cat sds,
  { all_drifts_ok cat sds } + { ~ all_drifts_ok cat sds }.
Proof.
  intros cat sds. induction sds as [|sd rest IH]; simpl.
  - left. exact I.
  - destruct (drift_ok_dec cat (sd_dr sd) (sd_h sd));
    destruct IH; try (left; tauto); right; tauto.
Qed.

Lemma all_pdelta_ok_dec : forall sds,
  { all_pdelta_ok sds } + { ~ all_pdelta_ok sds }.
Proof.
  induction sds as [|sd rest IH]; simpl.
  - left. exact I.
  - destruct (Rle_dec (sd_theta sd) (3/10));
    destruct IH; try (left; tauto); right; tauto.
Qed.

(* Helper: decidability for mass_ratio_ok.                           *)
Lemma mass_ratio_ok_dec : forall m1 m2,
  { mass_ratio_ok m1 m2 } + { ~ mass_ratio_ok m1 m2 }.
Proof.
  intros. unfold mass_ratio_ok.
  destruct (Rle_dec m2 (3/2 * m1));
  destruct (Rle_dec m1 (3/2 * m2));
  try (left; tauto); right; tauto.
Qed.

Lemma stiffness_continuity_dec : forall k1 k2,
  { stiffness_continuity k1 k2 } + { ~ stiffness_continuity k1 k2 }.
Proof.
  intros. unfold stiffness_continuity. apply Rge_dec.
Qed.

Lemma all_adjacent_dec : forall {A : Type} (P : A -> A -> Prop)
    (P_dec : forall x y, { P x y } + { ~ P x y }) (l : list A),
  { all_adjacent P l } + { ~ all_adjacent P l }.
Proof.
  intros A P P_dec l. induction l as [|x l' IH]; simpl.
  - left. exact I.
  - destruct l' as [|y rest]; simpl.
    + left. exact I.
    + destruct (P_dec x y); destruct IH;
      try (left; tauto); right; tauto.
Qed.

Lemma elevation_regular_dec : forall masses stiffnesses,
  { elevation_regular masses stiffnesses } +
  { ~ elevation_regular masses stiffnesses }.
Proof.
  intros. unfold elevation_regular.
  destruct (all_adjacent_dec mass_ratio_ok mass_ratio_ok_dec masses);
  destruct (all_adjacent_dec stiffness_continuity stiffness_continuity_dec
              stiffnesses);
  try (left; tauto); right; tauto.
Qed.

Theorem ec8_compliant_dec : forall b sp sds,
  { ec8_compliant b sp sds } + { ~ ec8_compliant b sp sds }.
Proof.
  intros. unfold ec8_compliant.
  destruct (plan_regular_dec (bld_e0x b) (bld_e0y b)
              (bld_rx b) (bld_ry b) (bld_ls b));
  destruct (elevation_regular_dec (bld_masses b) (bld_stiffnesses b));
  destruct (Rle_dec (bld_T1 b) (4 * sp_TC (spar_sp sp)));
  destruct (all_drifts_ok_dec (spar_ns_cat sp) sds);
  destruct (all_pdelta_ok_dec sds);
  try (left; tauto); right; tauto.
Qed.

(* ================================================================ *)
(*  EXTRACTION — item 29                                             *)
(* ================================================================ *)

Require Import ExtrOcamlBasic ExtrOcamlNatInt.

(* Map Coq reals to OCaml floats for executable extraction.          *)
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant Rplus => "( +. )".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Rminus => "( -. )".
Extract Inlined Constant Rdiv => "(fun a b -> a /. b)".
Extract Inlined Constant Rinv => "(fun x -> 1.0 /. x)".
Extract Inlined Constant Rle_dec => "(fun a b -> if a <= b then true else false)".
Extract Inlined Constant Rge_dec => "(fun a b -> if a >= b then if a = b then true else true else false)".
Extract Inlined Constant Ropp => "(fun x -> ~-. x)".
Extract Inlined Constant Rabs => "(fun x -> Float.abs x)".
Extract Inlined Constant Rmax => "(fun a b -> if a >= b then a else b)".

Extraction "eurocode8.ml"
  ec8_compliant_dec
  Se Sd Fb Fi
  storey_forces sum_Fi_eq_Fb
  spectrum_lookup gamma_I q0
  classify_pdelta pdelta_amplification
  drift_limit lambda.
