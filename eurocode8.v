(******************************************************************************)
(*                                                                            *)
(*          Eurocode 8: Seismic Design Verification Predicates                *)
(*                                                                            *)
(*     Formalizes EN 1998-1:2004 seismic action definitions, response       *)
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
(*  GROUND TYPES — EN 1998-1:2004, clause 3.1.2                  *)
(* ================================================================ *)

Inductive ground_type : Type :=
  | GroundA | GroundB | GroundC | GroundD | GroundE.

(* ================================================================ *)
(*  SPECTRUM TYPES — EN 1998-1:2004, clause 3.2.2.2              *)
(* ================================================================ *)

Inductive spectrum_type : Type :=
  | Type1 | Type2.

(* ================================================================ *)
(*  IMPORTANCE CLASSES — EN 1998-1:2004, clause 4.2.5            *)
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

(* Well-formedness: corner periods are positive and ordered.         *)
Definition well_formed_spectrum (p : spectrum_params) : Prop :=
  sp_S p > 0 /\
  sp_TB p > 0 /\
  sp_TB p < sp_TC p /\
  sp_TC p < sp_TD p.

Lemma spectrum_lookup_wf : forall st gt,
  well_formed_spectrum (spectrum_lookup st gt).
Proof.
  intros st gt; destruct st, gt; unfold well_formed_spectrum; simpl; lra.
Qed.

(* ================================================================ *)
(*  ELASTIC RESPONSE SPECTRUM Se(T) — clause 3.2.2.2, eqs 3.2-3.5 *)
(* ================================================================ *)

(* Damping correction factor: eta = max(sqrt(10/(5+xi)), 0.55).      *)
(* For 5% damping (xi=5), eta = 1.  Per clause 3.2.2.2.             *)
Definition eta_min : R := 55 / 100.

(* Compute eta from damping ratio xi (percent).                        *)
(* eta = max(sqrt(10 / (5 + xi)), 0.55) per clause 3.2.2.2.          *)
Definition compute_eta (xi : R) : R :=
  Rmax (sqrt (10 / (5 + xi))) eta_min.

(* compute_eta always returns at least eta_min.                        *)
Lemma compute_eta_ge_min : forall xi,
  compute_eta xi >= eta_min.
Proof.
  intro. unfold compute_eta. apply Rle_ge. apply Rmax_r.
Qed.

(* At 5% damping, eta = 1.                                            *)
Lemma compute_eta_5 : compute_eta 5 = 1.
Proof.
  unfold compute_eta, eta_min.
  replace (10 / (5 + 5)) with 1 by field.
  rewrite sqrt_1.
  apply Rmax_left. lra.
Qed.

(* Se(T) for given spectrum parameters, reference PGA ag, and       *)
(* damping correction factor eta (eta = 1 for 5% damping).         *)

(* Se(T) is guarded: returns 0 for T < 0.  The standard defines Se    *)
(* only for T >= 0; the guard prevents physically meaningless results. *)
Definition Se (p : spectrum_params) (ag eta T : R) : R :=
  if Rle_dec 0 T then
    if Rle_dec T (sp_TB p) then
      ag * sp_S p * (1 + T / sp_TB p * (eta * (5 / 2) - 1))
    else if Rle_dec T (sp_TC p) then
      ag * sp_S p * eta * (5 / 2)
    else if Rle_dec T (sp_TD p) then
      ag * sp_S p * eta * (5 / 2) * (sp_TC p / T)
    else
      ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T * T))
  else
    0.

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
  destruct (Rle_dec 0 0) as [H0|H0]; [|exfalso; lra].
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
  destruct (Rle_dec 0 (sp_TB p)) as [H0|H0]; [|exfalso; lra].
  destruct (Rle_dec (sp_TB p) (sp_TB p)) as [H|H].
  - field. lra.
  - exfalso. lra.
Qed.

(* Se at T = TC equals the plateau value (branch 2 evaluation).       *)
Lemma Se_at_TC : forall p ag eta,
  sp_TB p > 0 ->
  sp_TB p < sp_TC p ->
  Se p ag eta (sp_TC p) = ag * sp_S p * eta * (5 / 2).
Proof.
  intros p ag eta HTB H.
  unfold Se.
  destruct (Rle_dec 0 (sp_TC p)) as [H0|H0]; [|exfalso; lra].
  destruct (Rle_dec (sp_TC p) (sp_TB p)) as [H1|H1].
  - exfalso. lra.
  - destruct (Rle_dec (sp_TC p) (sp_TC p)) as [H2|H2].
    + reflexivity.
    + exfalso. lra.
Qed.

(* Branch agreement at TC: plateau and 1/T branch agree at TC.       *)
Lemma Se_branch_agreement_at_TC : forall p ag eta,
  sp_TB p < sp_TC p ->
  sp_TC p > 0 ->
  Se p ag eta (sp_TC p) =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / sp_TC p).
Proof.
  intros p ag eta HTB HTC.
  unfold Se.
  destruct (Rle_dec 0 (sp_TC p)) as [H0|H0]; [|exfalso; lra].
  destruct (Rle_dec (sp_TC p) (sp_TB p)) as [H1|H1].
  - exfalso. lra.
  - destruct (Rle_dec (sp_TC p) (sp_TC p)) as [H2|H2].
    + field. lra.
    + exfalso. lra.
Qed.

(* Se at T = TD equals the descending-branch value ag*S*eta*2.5*TC/TD. *)
Lemma Se_at_TD : forall p ag eta,
  sp_TB p > 0 ->
  sp_TB p < sp_TD p ->
  sp_TC p < sp_TD p ->
  Se p ag eta (sp_TD p) =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / sp_TD p).
Proof.
  intros p ag eta HTB_pos HTB HTC.
  unfold Se.
  destruct (Rle_dec 0 (sp_TD p)) as [H0|H0]; [|exfalso; lra].
  destruct (Rle_dec (sp_TD p) (sp_TB p)) as [H1|H1].
  - exfalso. lra.
  - destruct (Rle_dec (sp_TD p) (sp_TC p)) as [H2|H2].
    + exfalso. lra.
    + destruct (Rle_dec (sp_TD p) (sp_TD p)) as [H3|H3].
      * reflexivity.
      * exfalso. lra.
Qed.

(* Branch agreement at TD: 1/T and 1/T^2 branches agree at TD.       *)
Lemma Se_branch_agreement_at_TD : forall p ag eta,
  sp_TB p < sp_TD p ->
  sp_TC p < sp_TD p ->
  sp_TD p > 0 ->
  Se p ag eta (sp_TD p) =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (sp_TD p * sp_TD p)).
Proof.
  intros p ag eta HTB HTC HTD.
  unfold Se.
  destruct (Rle_dec 0 (sp_TD p)) as [H0|H0]; [|exfalso; lra].
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
  destruct (Rle_dec 0 T1) as [HT1g|HT1g]; [|exfalso; lra].
  destruct (Rle_dec 0 T2) as [HT2g|HT2g]; [|exfalso; lra].
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
  sp_TB p > 0 ->
  sp_TB p < T -> T <= sp_TC p ->
  Se p ag eta T = ag * sp_S p * eta * (5 / 2).
Proof.
  intros p ag eta T HTB_pos HTB HTC.
  unfold Se.
  destruct (Rle_dec 0 T) as [H0|H0]; [|exfalso; lra].
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
    destruct (Rle_dec 0 T1); [|exfalso; lra].
    destruct (Rle_dec T1 (sp_TB p)); [lra|].
    destruct (Rle_dec T1 (sp_TC p)); [lra|].
    destruct (Rle_dec T1 (sp_TD p)); [reflexivity|lra]. }
  assert (HSeT2: Se p ag eta T2 =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / T2)).
  { unfold Se.
    destruct (Rle_dec 0 T2); [|exfalso; lra].
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
    destruct (Rle_dec 0 T1); [|exfalso; lra].
    destruct (Rle_dec T1 (sp_TB p)); [lra|].
    destruct (Rle_dec T1 (sp_TC p)); [lra|].
    destruct (Rle_dec T1 (sp_TD p)); [lra|].
    reflexivity. }
  assert (HSeT2: Se p ag eta T2 =
    ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T2 * T2))).
  { unfold Se.
    destruct (Rle_dec 0 T2); [|exfalso; lra].
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

(* Se(T) >= 0 for non-negative inputs.                               *)
Lemma Se_nonneg : forall p ag eta T,
  well_formed_spectrum p ->
  ag >= 0 -> eta >= 0 -> T >= 0 ->
  eta * (5 / 2) >= 1 ->
  Se p ag eta T >= 0.
Proof.
  intros p ag eta T [HS [HTB [HTBC HTCD]]] Hag Heta HT Heta25.
  unfold Se.
  destruct (Rle_dec 0 T) as [HT0|HT0]; [|exfalso; lra].
  destruct (Rle_dec T (sp_TB p)).
  - apply Rle_ge. apply Rmult_le_pos.
    + apply Rmult_le_pos; lra.
    + assert (T / sp_TB p >= 0) by (unfold Rdiv; apply Rle_ge;
        apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
      assert (eta * (5 / 2) - 1 >= 0) by lra.
      assert (T / sp_TB p * (eta * (5 / 2) - 1) >= 0) by
        (apply Rle_ge; apply Rmult_le_pos; lra).
      lra.
  - destruct (Rle_dec T (sp_TC p)).
    + apply Rle_ge. apply Rmult_le_pos.
      * apply Rmult_le_pos; [apply Rmult_le_pos|]; lra.
      * lra.
    + destruct (Rle_dec T (sp_TD p)).
      * apply Rle_ge. apply Rmult_le_pos.
        -- apply Rmult_le_pos; [apply Rmult_le_pos;
             [apply Rmult_le_pos|]|]; lra.
        -- unfold Rdiv. apply Rmult_le_pos; [lra|].
           left. apply Rinv_0_lt_compat. lra.
      * apply Rle_ge. apply Rmult_le_pos.
        -- apply Rmult_le_pos; [apply Rmult_le_pos;
             [apply Rmult_le_pos|]|]; lra.
        -- unfold Rdiv. apply Rmult_le_pos.
           ++ apply Rmult_le_pos; lra.
           ++ left. apply Rinv_0_lt_compat.
              apply Rmult_lt_0_compat; lra.
Qed.

(* ================================================================ *)
(*  CONTINUITY OF Se ON (0, +inf)                                   *)
(* ================================================================ *)

(* Se without the T >= 0 guard.  Equals Se for T > 0.               *)
Definition Se_inner (p : spectrum_params) (ag eta T : R) : R :=
  if Rle_dec T (sp_TB p) then
    ag * sp_S p * (1 + T / sp_TB p * (eta * (5 / 2) - 1))
  else if Rle_dec T (sp_TC p) then
    ag * sp_S p * eta * (5 / 2)
  else if Rle_dec T (sp_TD p) then
    ag * sp_S p * eta * (5 / 2) * (sp_TC p / T)
  else
    ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T * T)).

Lemma Se_eq_inner : forall p ag eta T,
  T > 0 -> Se p ag eta T = Se_inner p ag eta T.
Proof.
  intros. unfold Se, Se_inner.
  destruct (Rle_dec 0 T); [reflexivity | lra].
Qed.

(* Piecewise function is continuous at a join point if both branches *)
(* are continuous there and agree on the value.                      *)
Lemma piecewise_cont_at :
  forall (f g : R -> R) (c : R),
  continuity_pt f c -> continuity_pt g c -> f c = g c ->
  continuity_pt (fun x => if Rle_dec x c then f x else g x) c.
Proof.
  intros f g c Hf Hg Hfg.
  unfold continuity_pt, continue_in, limit1_in, limit_in in *.
  unfold D_x, no_cond in *. simpl in *.
  intros eps Heps.
  destruct (Hf eps Heps) as [d1 [Hd1 Hf']]; clear Hf.
  destruct (Hg eps Heps) as [d2 [Hd2 Hg']]; clear Hg.
  exists (Rmin d1 d2). split; [apply Rmin_pos; assumption |].
  intros x [[_ Hneq] Hdist].
  destruct (Rle_dec c c) as [_ | Hn]; [| exfalso; lra].
  destruct (Rle_dec x c).
  - apply Hf'. split; [split; [exact I | exact Hneq] |].
    eapply Rlt_le_trans; [exact Hdist | apply Rmin_l].
  - rewrite Hfg. apply Hg'. split; [split; [exact I | exact Hneq] |].
    eapply Rlt_le_trans; [exact Hdist | apply Rmin_r].
Qed.

(* Se is continuous at every T > 0.  Proof by composing branch       *)
(* continuity with branch agreement at corner periods TB, TC, TD.    *)
Theorem Se_continuous_pos : forall p ag eta T,
  well_formed_spectrum p -> T > 0 ->
  continuity_pt (Se p ag eta) T.
Proof.
  intros p ag eta T [HS [HTB [HTBC HTCD]]] HT.
  (* Step 1: Se = Se_inner near T since T > 0 *)
  apply continuity_pt_locally_ext with (f := Se_inner p ag eta) (a := T / 2).
  { lra. }
  { intros y Hy. symmetry. apply Se_eq_inner.
    unfold R_dist in Hy. assert (Hbd := Rabs_def2 _ _ Hy). lra. }
  (* Step 2: Se_inner continuity at T by case analysis *)
  unfold Se_inner.
  (* --- Breakpoint T = TB --- *)
  destruct (Req_EM_T T (sp_TB p)) as [-> | HT_neq_TB].
  { apply piecewise_cont_at.
    - reg; lra.
    - apply continuity_pt_locally_ext with
        (f := fun _ : R => ag * sp_S p * eta * (5 / 2))
        (a := sp_TC p - sp_TB p).
      { lra. }
      { intros y Hy. unfold R_dist in Hy.
        assert (Hbd := Rabs_def2 _ _ Hy).
        destruct (Rle_dec y (sp_TC p)); [reflexivity | exfalso; lra]. }
      apply continuity_pt_const. unfold constant. reflexivity.
    - destruct (Rle_dec (sp_TB p) (sp_TC p)); [| lra]. field. lra. }
  (* --- T not at TB --- *)
  destruct (Rle_dec T (sp_TB p)) as [HT_le_TB | HT_gt_TB].
  { (* 0 < T < TB: interior of branch 1 *)
    apply continuity_pt_locally_ext with
      (f := fun T0 => ag * sp_S p *
        (1 + T0 / sp_TB p * (eta * (5 / 2) - 1)))
      (a := Rmin (T / 2) (sp_TB p - T)).
    { apply Rmin_pos; lra. }
    { intros y Hy. unfold R_dist in Hy.
      assert (Hbd := Rabs_def2 _ _ Hy).
      assert (Hy_ub : y < sp_TB p).
      { apply Rlt_le_trans with (T + (sp_TB p - T)).
        - apply Rlt_le_trans with (T + Rmin (T / 2) (sp_TB p - T));
            [lra | apply Rplus_le_compat_l; apply Rmin_r].
        - lra. }
      destruct (Rle_dec y (sp_TB p)); [reflexivity | lra]. }
    reg; lra. }
  (* --- T > TB: peel off outer branch --- *)
  apply continuity_pt_locally_ext with
    (f := fun T0 =>
      if Rle_dec T0 (sp_TC p) then
        ag * sp_S p * eta * (5 / 2)
      else if Rle_dec T0 (sp_TD p) then
        ag * sp_S p * eta * (5 / 2) * (sp_TC p / T0)
      else
        ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T0 * T0)))
    (a := (T - sp_TB p) / 2).
  { lra. }
  { intros y Hy. unfold R_dist in Hy.
    assert (Hbd := Rabs_def2 _ _ Hy).
    destruct (Rle_dec y (sp_TB p)); [exfalso; lra | reflexivity]. }
  (* --- Breakpoint T = TC --- *)
  destruct (Req_EM_T T (sp_TC p)) as [-> | HT_neq_TC].
  { apply piecewise_cont_at.
    - apply continuity_pt_const. unfold constant. reflexivity.
    - apply continuity_pt_locally_ext with
        (f := fun T0 => ag * sp_S p * eta * (5 / 2) * (sp_TC p / T0))
        (a := sp_TD p - sp_TC p).
      { lra. }
      { intros y Hy. unfold R_dist in Hy.
        assert (Hbd := Rabs_def2 _ _ Hy).
        destruct (Rle_dec y (sp_TD p)); [reflexivity | exfalso; lra]. }
      reg; lra.
    - destruct (Rle_dec (sp_TC p) (sp_TD p)); [| lra]. field. lra. }
  (* --- T not at TC --- *)
  destruct (Rle_dec T (sp_TC p)) as [HT_le_TC | HT_gt_TC].
  { (* TB < T < TC: constant branch *)
    apply continuity_pt_locally_ext with
      (f := fun _ : R => ag * sp_S p * eta * (5 / 2))
      (a := Rmin (T - sp_TB p) (sp_TC p - T)).
    { apply Rmin_pos; lra. }
    { intros y Hy. unfold R_dist in Hy.
      assert (Hbd := Rabs_def2 _ _ Hy).
      assert (Hy_ub : y < sp_TC p).
      { apply Rlt_le_trans with (T + (sp_TC p - T)).
        - apply Rlt_le_trans with (T + Rmin (T - sp_TB p) (sp_TC p - T));
            [lra | apply Rplus_le_compat_l; apply Rmin_r].
        - lra. }
      destruct (Rle_dec y (sp_TC p)); [reflexivity | lra]. }
    apply continuity_pt_const. unfold constant. reflexivity. }
  (* --- T > TC: peel off TC branch --- *)
  apply continuity_pt_locally_ext with
    (f := fun T0 =>
      if Rle_dec T0 (sp_TD p) then
        ag * sp_S p * eta * (5 / 2) * (sp_TC p / T0)
      else
        ag * sp_S p * eta * (5 / 2) * (sp_TC p * sp_TD p / (T0 * T0)))
    (a := (T - sp_TC p) / 2).
  { lra. }
  { intros y Hy. unfold R_dist in Hy.
    assert (Hbd := Rabs_def2 _ _ Hy).
    destruct (Rle_dec y (sp_TC p)); [exfalso; lra | reflexivity]. }
  (* --- Breakpoint T = TD --- *)
  destruct (Req_EM_T T (sp_TD p)) as [-> | HT_neq_TD].
  { apply piecewise_cont_at.
    - reg; lra.
    - reg. intro H. assert (sp_TD p > 0) by lra.
      apply Rmult_integral in H. lra.
    - field. lra. }
  (* --- T not at TD --- *)
  destruct (Rle_dec T (sp_TD p)) as [HT_le_TD | HT_gt_TD].
  { (* TC < T < TD: branch 3 *)
    apply continuity_pt_locally_ext with
      (f := fun T0 => ag * sp_S p * eta * (5 / 2) * (sp_TC p / T0))
      (a := Rmin (T - sp_TC p) (sp_TD p - T)).
    { apply Rmin_pos; lra. }
    { intros y Hy. unfold R_dist in Hy.
      assert (Hbd := Rabs_def2 _ _ Hy).
      assert (Hy_ub : y < sp_TD p).
      { apply Rlt_le_trans with (T + (sp_TD p - T)).
        - apply Rlt_le_trans with (T + Rmin (T - sp_TC p) (sp_TD p - T));
            [lra | apply Rplus_le_compat_l; apply Rmin_r].
        - lra. }
      destruct (Rle_dec y (sp_TD p)); [reflexivity | lra]. }
    reg; lra. }
  { (* T > TD: branch 4 *)
    apply continuity_pt_locally_ext with
      (f := fun T0 => ag * sp_S p * eta * (5 / 2) *
        (sp_TC p * sp_TD p / (T0 * T0)))
      (a := (T - sp_TD p) / 2).
    { lra. }
    { intros y Hy. unfold R_dist in Hy.
      assert (Hbd := Rabs_def2 _ _ Hy).
      destruct (Rle_dec y (sp_TD p)); [exfalso; lra | reflexivity]. }
    reg. intro H. apply Rmult_integral in H. lra. }
Qed.

(* ================================================================ *)
(*  VERTICAL SEISMIC ACTION — EN 1998-1:2004, clause 3.2.2.3      *)
(* ================================================================ *)

(* Vertical spectrum parameters: TB = 0.05, TC = 0.15, TD = 1.0.    *)
(* S = 1 (no soil amplification for vertical component).             *)
Definition vertical_spectrum_params : spectrum_params :=
  mk_spectrum_params 1 (1/20) (3/20) 1.

(* Ratio avg/ag depends on spectrum type.                            *)
(* Type 1: avg = 0.90 * ag.  Type 2: avg = 0.45 * ag.               *)
Definition avg_ratio (st : spectrum_type) : R :=
  match st with
  | Type1 => 9/10
  | Type2 => 9/20
  end.

(* Vertical elastic response spectrum, reusing Se.                   *)
Definition Sve (st : spectrum_type) (ag eta T : R) : R :=
  Se vertical_spectrum_params (avg_ratio st * ag) eta T.

Lemma vertical_spectrum_wf : well_formed_spectrum vertical_spectrum_params.
Proof.
  unfold well_formed_spectrum, vertical_spectrum_params. simpl. lra.
Qed.

(* ================================================================ *)
(*  DUCTILITY CLASSES — EN 1998-1:2004, clause 5.2.1              *)
(* ================================================================ *)

Inductive ductility_class : Type :=
  | DCL | DCM | DCH.

(* ================================================================ *)
(*  STRUCTURAL SYSTEM TYPES — EN 1998-1:2004, Table 5.1           *)
(* ================================================================ *)

Inductive structural_system : Type :=
  | FrameSystem
  | DualFrameEquiv
  | DualWallEquiv
  | DuctileWallSystem
  | InvertedPendulum
  | TorsionallyFlexible.

(* ================================================================ *)
(*  BEHAVIOR FACTOR q0 — EN 1998-1:2004, Table 5.1                *)
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
  | DCM, DualWallEquiv         => 3 * au_a1
  | DCM, DuctileWallSystem     => 3 * au_a1
  | DCM, InvertedPendulum      => 3 / 2
  | DCM, TorsionallyFlexible   => 2
  | DCH, FrameSystem           => 9 / 2 * au_a1
  | DCH, DualFrameEquiv        => 9 / 2 * au_a1
  | DCH, DualWallEquiv         => 4 * au_a1
  | DCH, DuctileWallSystem     => 4 * au_a1
  | DCH, InvertedPendulum      => 2
  | DCH, TorsionallyFlexible   => 3
  end.

(* q0 >= 1 for all valid inputs (au_a1 >= 1).                       *)
Lemma q0_ge_1 : forall dc ss au_a1,
  au_a1 >= 1 -> q0 dc ss au_a1 >= 1.
Proof.
  intros dc ss au_a1 Ha; destruct dc, ss; simpl; lra.
Qed.

(* q0 upper bound: q0 <= 9/2 * au_a1 for all cases.                 *)
Lemma q0_upper : forall dc ss au_a1,
  au_a1 >= 1 -> q0 dc ss au_a1 <= 9 / 2 * au_a1.
Proof.
  intros dc ss au_a1 Ha; destruct dc, ss; simpl; lra.
Qed.

(* ================================================================ *)
(*  DESIGN SPECTRUM Sd(T) — EN 1998-1:2004, clause 3.2.2.5        *)
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
(*  LATERAL FORCE METHOD — EN 1998-1:2004, clause 4.3.3.2         *)
(* ================================================================ *)

(* Applicability: T1 <= 4*TC and the building is regular in          *)
(* elevation.                                                        *)
Definition lateral_force_applicable (T1 : R) (p : spectrum_params)
    (elevation_regular : Prop) : Prop :=
  T1 <= 4 * sp_TC p /\ elevation_regular.

(* ================================================================ *)
(*  BASE SHEAR — EN 1998-1:2004, clause 4.3.3.2.2                 *)
(* ================================================================ *)

(* Correction factor lambda: 0.85 if T1 <= 2*TC and >= 3 storeys,   *)
(* 1.0 otherwise.                                                   *)
Definition lambda (T1 : R) (p : spectrum_params) (n_storeys : nat) : R :=
  if Rle_dec T1 (2 * sp_TC p) then
    if Nat.leb 3 n_storeys then 17 / 20 else 1
  else
    1.

(* lambda always returns 17/20 or 1.                                 *)
Lemma lambda_values : forall T1 p n,
  lambda T1 p n = 17 / 20 \/ lambda T1 p n = 1.
Proof.
  intros. unfold lambda.
  destruct (Rle_dec T1 (2 * sp_TC p)).
  - destruct (Nat.leb 3 n); [left | right]; reflexivity.
  - right. reflexivity.
Qed.

(* Base shear force Fb.                                              *)
Definition Fb (sd_T1 m : R) (lam : R) : R := sd_T1 * m * lam.

(* ================================================================ *)
(*  ACCIDENTAL TORSION — EN 1998-1:2004, clause 4.3.3.2.4         *)
(* ================================================================ *)

(* Amplification factor for accidental torsional effects.             *)
(* delta = 1 + 0.6 * x / Le, where x is the distance from the       *)
(* centre of mass and Le is the distance between the two outermost   *)
(* lateral load-resisting elements.  Applied to storey forces.       *)
Definition torsion_amplification (x Le : R) : R :=
  1 + 3/5 * x / Le.

(* delta >= 1 for non-negative x and positive Le.                    *)
Lemma torsion_amp_ge_1 : forall x Le,
  x >= 0 -> Le > 0 -> torsion_amplification x Le >= 1.
Proof.
  intros x Le Hx HLe. unfold torsion_amplification.
  assert (3/5 * x / Le >= 0).
  { unfold Rdiv. apply Rle_ge.
    apply Rmult_le_pos.
    - apply Rmult_le_pos; lra.
    - left. apply Rinv_0_lt_compat. lra. }
  lra.
Qed.

(* Maximum delta occurs at x = Le/2 (outermost position).            *)
Lemma torsion_amp_max : forall Le,
  Le > 0 -> torsion_amplification (Le / 2) Le = 13/10.
Proof.
  intros Le HLe. unfold torsion_amplification. field. lra.
Qed.

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

(* End-to-end: for valid inputs, Sd >= 0, Fb >= 0, ΣFi = Fb.        *)
Lemma pipeline_valid : forall st gt ag eta q T1 m lam storeys,
  ag >= 0 -> eta >= 0 -> q >= 1 -> m >= 0 -> lam > 0 ->
  T1 >= 0 -> eta * (5 / 2) >= 1 ->
  sum_zm storeys > 0 ->
  let p := spectrum_lookup st gt in
  let sd_val := Sd p ag eta q T1 in
  let base := Fb sd_val m lam in
  sd_val >= 0 /\ base >= 0 /\
  sum_R (storey_forces base storeys) = base.
Proof.
  intros st gt ag eta q T1 m lam storeys
    Hag Heta Hq Hm Hlam HT1 Heta25 Hszm.
  simpl. split; [|split].
  - unfold Sd. apply Rle_ge. apply Rle_trans with (beta * ag).
    + unfold beta. apply Rmult_le_pos; lra.
    + apply Rmax_r.
  - unfold Fb. apply Rle_ge.
    apply Rmult_le_pos; [apply Rmult_le_pos|lra].
    + apply Rle_trans with (beta * ag).
      * unfold beta. apply Rmult_le_pos; lra.
      * unfold Sd. apply Rmax_r.
    + lra.
  - apply sum_Fi_eq_Fb. exact Hszm.
Qed.

(* ================================================================ *)
(*  DISPLACEMENT AMPLIFICATION — EN 1998-1:2004, clause 4.3.4     *)
(* ================================================================ *)

(* Design displacement = q * elastic displacement.                   *)
(* The drift check requires dr to already include this factor, i.e.  *)
(* dr = q * dr_elastic.                                              *)
Definition ds (q de : R) : R := q * de.

(* ================================================================ *)
(*  COMBINATION OF SEISMIC COMPONENTS — clause 4.3.3.5.1            *)
(* ================================================================ *)

(* SRSS combination: E = sqrt(Ex^2 + Ey^2).                          *)
Definition combine_srss (ex ey : R) : R :=
  sqrt (ex * ex + ey * ey).

(* 100%+30% rule: E = max(|Ex|+0.30*|Ey|, 0.30*|Ex|+|Ey|).          *)
Definition combine_30pct (ex ey : R) : R :=
  Rmax (Rabs ex + 3/10 * Rabs ey) (3/10 * Rabs ex + Rabs ey).

(* Both methods are permitted by the code; neither dominates the     *)
(* other in general (SRSS > 30% when ex ≈ ey, 30% > SRSS when one   *)
(* component dominates).                                             *)

(* SRSS is non-negative.                                             *)
Lemma combine_srss_nonneg : forall ex ey,
  combine_srss ex ey >= 0.
Proof.
  intros. unfold combine_srss.
  apply Rle_ge. apply sqrt_pos.
Qed.

(* 30% rule is non-negative.                                         *)
Lemma combine_30pct_nonneg : forall ex ey,
  combine_30pct ex ey >= 0.
Proof.
  intros. unfold combine_30pct.
  apply Rle_ge.
  apply Rle_trans with (Rabs ex + 3/10 * Rabs ey).
  - generalize (Rabs_pos ex). generalize (Rabs_pos ey). lra.
  - apply Rmax_l.
Qed.

(* ================================================================ *)
(*  DRIFT LIMITS — EN 1998-1:2004, clause 4.4.3.2                 *)
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

(* Reduction factor nu for lower return period per importance class.  *)
(* EN 1998-1:2004, clause 4.4.3.2: recommended values.            *)
Definition nu (ic : importance_class) : R :=
  match ic with
  | ClassI   => 2 / 5
  | ClassII  => 2 / 5
  | ClassIII => 1 / 2
  | ClassIV  => 1 / 2
  end.

(* Drift check: dr * nu <= drift_limit * h.                          *)
Definition drift_ok (ic : importance_class) (cat : ns_category)
    (dr h : R) : Prop :=
  dr * nu ic <= drift_limit cat * h.

(* Drift check is decidable.                                         *)
Lemma drift_ok_dec : forall ic cat dr h,
  { drift_ok ic cat dr h } + { ~ drift_ok ic cat dr h }.
Proof.
  intros. unfold drift_ok.
  apply Rle_dec.
Defined.

(* Ductile drift limit is strictly more permissive than brittle.     *)
Lemma drift_ductile_more_permissive : forall ic dr h,
  h > 0 -> drift_ok ic NS_Brittle dr h -> drift_ok ic NS_Ductile dr h.
Proof.
  intros ic dr h Hh Hb. unfold drift_ok in *.
  simpl in *. lra.
Qed.

(* None is more permissive than ductile.                             *)
Lemma drift_none_more_permissive : forall ic dr h,
  h > 0 -> drift_ok ic NS_Ductile dr h -> drift_ok ic NS_None dr h.
Proof.
  intros ic dr h Hh Hd. unfold drift_ok in *.
  simpl in *. lra.
Qed.

(* Full ordering: None >= Ductile >= Brittle.                        *)
Lemma drift_ordering : forall ic dr h,
  h > 0 -> drift_ok ic NS_Brittle dr h -> drift_ok ic NS_None dr h.
Proof.
  intros. apply drift_none_more_permissive; [assumption|].
  apply drift_ductile_more_permissive; assumption.
Qed.

(* ================================================================ *)
(*  P-DELTA EFFECTS — EN 1998-1:2004, clause 4.4.2.2              *)
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

(* Analysis type for P-delta: determines the permissible theta_max.  *)
(* PDA_Simplified: approximate 1/(1-theta) amplification, theta <= 0.20. *)
(* PDA_Explicit: explicit second-order analysis, theta <= 0.30.      *)
Inductive pdelta_analysis : Type :=
  | PDA_Simplified
  | PDA_Explicit.

Definition pdelta_theta_max (pa : pdelta_analysis) : R :=
  match pa with
  | PDA_Simplified => 1/5
  | PDA_Explicit   => 3/10
  end.

(* 1/(1-theta) is strictly increasing on (-inf, 1).                  *)
Lemma pdelta_amp_increasing : forall th1 th2,
  th1 < th2 -> th2 < 1 ->
  pdelta_amplification th1 < pdelta_amplification th2.
Proof.
  intros th1 th2 H12 H2.
  unfold pdelta_amplification, Rdiv.
  rewrite !Rmult_1_l.
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; lra.
  - lra.
Qed.

(* ================================================================ *)
(*  REGULARITY — EN 1998-1:2004, clause 4.2.3                     *)
(* ================================================================ *)

(* Plan regularity: compactness (clause 4.2.3.2), eccentricity       *)
(* <= 0.30*r, torsional radius >= ls.                                *)
Definition plan_regular (e0x e0y rx ry ls compactness : R) : Prop :=
  compactness >= 19/20 /\
  Rabs e0x <= 3/10 * rx /\
  Rabs e0y <= 3/10 * ry /\
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
(* Lists are ordered ground floor first: [k_storey1, k_storey2, ...] *)
(* all_adjacent checks consecutive pairs (k_i, k_{i+1}) bottom-up.  *)
Definition stiffness_continuity (k_below k_above : R) : Prop :=
  k_below >= 7/10 * k_above.

(* Stiffness must be >= 80% of average of three storeys above.        *)
(* Clause 4.2.3.3: k_i >= 0.8 * (k_{i+1} + k_{i+2} + k_{i+3}) / 3. *)
(* Only applies when at least three storeys exist above.              *)
Fixpoint stiffness_avg3_ok (ks : list R) : Prop :=
  match ks with
  | k :: ((k1 :: k2 :: k3 :: _) as rest) =>
      k >= 4/5 * ((k1 + k2 + k3) / 3) /\
      stiffness_avg3_ok rest
  | _ => True
  end.

(* Setback constraint: upper storey plan area >= 80% of lower.        *)
(* Clause 4.2.3.3: setbacks shall not exceed 20% at any floor.       *)
Definition setback_ok (area_below area_above : R) : Prop :=
  area_above >= 4/5 * area_below.

(* Lists ordered ground floor first.                                  *)
Definition elevation_regular (masses stiffnesses plan_areas : list R)
    : Prop :=
  all_adjacent mass_ratio_ok masses /\
  all_adjacent stiffness_continuity stiffnesses /\
  stiffness_avg3_ok stiffnesses /\
  all_adjacent setback_ok plan_areas.

(* Plan-regular and elevation-regular implies lateral force method    *)
(* is applicable (given the period condition T1 <= 4*TC).            *)
Lemma regularity_implies_lfm :
  forall T1 p e0x e0y rx ry ls c masses stiffs areas,
  plan_regular e0x e0y rx ry ls c ->
  elevation_regular masses stiffs areas ->
  T1 <= 4 * sp_TC p ->
  lateral_force_applicable T1 p (elevation_regular masses stiffs areas).
Proof.
  intros. unfold lateral_force_applicable. split; assumption.
Qed.

(* ================================================================ *)
(*  FULL COMPLIANCE PREDICATE — composing all checks                *)
(* ================================================================ *)

Record building : Type := mk_building {
  bld_storeys      : list storey;
  bld_stiffnesses_x: list R;  (* per-storey lateral stiffness, x direction *)
  bld_stiffnesses_y: list R;  (* per-storey lateral stiffness, y direction *)
  bld_weights      : list R;  (* per-storey gravity load in seismic design situation *)
  bld_T1_x         : R;       (* fundamental period, x direction *)
  bld_T1_y         : R;       (* fundamental period, y direction *)
  bld_dc           : ductility_class;
  bld_ss           : structural_system;
  bld_au_a1        : R;       (* overstrength ratio αu/α1 *)
  bld_e0x          : R;       (* eccentricity x *)
  bld_e0y          : R;       (* eccentricity y *)
  bld_rx           : R;       (* torsional radius x *)
  bld_ry           : R;       (* torsional radius y *)
  bld_ls           : R;       (* radius of gyration *)
  bld_compactness  : R;       (* plan area / convex hull area *)
  bld_plan_areas   : list R;  (* per-storey plan area, ground up *)
}.

(* Derived fields.                                                    *)
Definition bld_masses (b : building) : list R :=
  map st_m (bld_storeys b).

Definition bld_n_storeys (b : building) : nat :=
  length (bld_storeys b).

(* Storey heights must be strictly increasing from base (cumulative). *)
(* st_z is height above base, not individual storey height.           *)
Fixpoint strictly_increasing_aux (prev : R) (l : list storey) : Prop :=
  match l with
  | nil => True
  | s :: rest => st_z s > prev /\ strictly_increasing_aux (st_z s) rest
  end.

Definition strictly_increasing (l : list storey) : Prop :=
  strictly_increasing_aux 0 l.

(* Building well-formedness: values sensible, lists match in length.  *)
Definition well_formed_building (b : building) : Prop :=
  length (bld_stiffnesses_x b) = length (bld_storeys b) /\
  length (bld_stiffnesses_y b) = length (bld_storeys b) /\
  length (bld_weights b) = length (bld_storeys b) /\
  length (bld_plan_areas b) = length (bld_storeys b) /\
  strictly_increasing (bld_storeys b) /\
  Forall (fun s => st_m s > 0) (bld_storeys b) /\
  Forall (fun k => k > 0) (bld_stiffnesses_x b) /\
  Forall (fun k => k > 0) (bld_stiffnesses_y b) /\
  Forall (fun w => w > 0) (bld_weights b) /\
  Forall (fun a => a > 0) (bld_plan_areas b) /\
  bld_T1_x b > 0 /\
  bld_T1_y b > 0 /\
  bld_au_a1 b >= 1.

Record seismic_params : Type := mk_seismic_params {
  spar_ic     : importance_class;
  spar_sp     : spectrum_params;
  spar_agR    : R;       (* reference peak ground acceleration *)
  spar_xi     : R;       (* damping ratio in percent *)
  spar_q      : R;
  spar_ns_cat : ns_category;
  spar_pda    : pdelta_analysis;
}.

(* Derived damping correction factor from damping ratio.               *)
Definition spar_eta (sp : seismic_params) : R :=
  compute_eta (spar_xi sp).

(* Design ground acceleration: ag = γI * agR.                        *)
Definition spar_ag (sp : seismic_params) : R :=
  gamma_I (spar_ic sp) * spar_agR sp.

(* ================================================================ *)
(*  COMPUTED STOREY DATA — derived from building model               *)
(* ================================================================ *)

(* Interstorey heights from cumulative storey elevations.            *)
Fixpoint storey_heights_aux (prev_z : R) (storeys : list storey)
    : list R :=
  match storeys with
  | nil => nil
  | s :: rest => (st_z s - prev_z) :: storey_heights_aux (st_z s) rest
  end.

Definition storey_heights (storeys : list storey) : list R :=
  storey_heights_aux 0 storeys.

(* Suffix sums: [x1;x2;x3] -> [x1+x2+x3; x2+x3; x3].             *)
(* Used for cumulative shear and gravity loads from top.             *)
Fixpoint suffix_sums (l : list R) : list R :=
  match l with
  | nil => nil
  | x :: rest => (x + sum_R rest) :: suffix_sums rest
  end.

(* Storey shears: cumulative lateral forces from top.                *)
Definition storey_shears (fb : R) (storeys : list storey) : list R :=
  suffix_sums (storey_forces fb storeys).

(* Gravity loads above each storey (suffix sum of weights).          *)
Definition storey_gravities (weights : list R) : list R :=
  suffix_sums weights.

(* Zip two lists with a binary operation.                            *)
Fixpoint zip_with {A B C : Type} (f : A -> B -> C)
    (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | x :: r1, y :: r2 => f x y :: zip_with f r1 r2
  | _, _ => nil
  end.

(* Design interstorey drifts: dr_i = q * V_i / k_i.                 *)
Definition storey_drifts (q : R) (shears stiffnesses : list R)
    : list R :=
  zip_with (fun v k => q * v / k) shears stiffnesses.

(* Per-storey verification data for drift and P-Delta checks.       *)
Record storey_data : Type := mk_storey_data {
  sd_dr    : R;   (* design interstorey drift *)
  sd_h     : R;   (* storey height *)
  sd_Ptot  : R;   (* total gravity load above this storey *)
  sd_Vtot  : R;   (* total seismic shear at this storey *)
}.

(* Derive theta from storey data fields.                             *)
Definition sd_theta (sd : storey_data) : R :=
  theta (sd_Ptot sd) (sd_dr sd) (sd_Vtot sd) (sd_h sd).

(* Build storey_data list from four parallel lists.                  *)
Fixpoint build_storey_data (drs hs ps vs : list R) : list storey_data :=
  match drs, hs, ps, vs with
  | dr :: drs', h :: hs', p :: ps', v :: vs' =>
      mk_storey_data dr h p v :: build_storey_data drs' hs' ps' vs'
  | _, _, _, _ => nil
  end.

(* Compute storey data for one direction given stiffnesses and T1.   *)
Definition compute_storey_data (b : building) (sp : seismic_params)
    (stiffnesses : list R) (T1 : R) : list storey_data :=
  let lam := lambda T1 (spar_sp sp) (bld_n_storeys b) in
  let ag := gamma_I (spar_ic sp) * spar_agR sp in
  let sd_val := Sd (spar_sp sp) ag (spar_eta sp) (spar_q sp) T1 in
  let m_total := sum_R (map st_m (bld_storeys b)) in
  let base_shear := Fb sd_val m_total lam in
  let shears := storey_shears base_shear (bld_storeys b) in
  let heights := storey_heights (bld_storeys b) in
  let gravities := storey_gravities (bld_weights b) in
  let drifts := storey_drifts (spar_q sp) shears stiffnesses in
  build_storey_data drifts heights gravities shears.

Fixpoint all_drifts_ok (ic : importance_class) (cat : ns_category)
    (sds : list storey_data) : Prop :=
  match sds with
  | nil => True
  | sd :: rest =>
      drift_ok ic cat (sd_dr sd) (sd_h sd) /\ all_drifts_ok ic cat rest
  end.

(* theta_max = 0.10 for negligible, 0.20 for simplified analysis,    *)
(* 0.30 for detailed second-order.                                   *)
Fixpoint all_pdelta_ok (theta_max : R) (sds : list storey_data) : Prop :=
  match sds with
  | nil => True
  | sd :: rest => sd_theta sd <= theta_max /\ all_pdelta_ok theta_max rest
  end.

Definition ec8_compliant (b : building) (sp : seismic_params) : Prop :=
  let sds_x := compute_storey_data b sp (bld_stiffnesses_x b) (bld_T1_x b) in
  let sds_y := compute_storey_data b sp (bld_stiffnesses_y b) (bld_T1_y b) in
  well_formed_building b /\
  well_formed_spectrum (spar_sp sp) /\
  spar_q sp = q0 (bld_dc b) (bld_ss b) (bld_au_a1 b) /\
  spar_xi sp >= 0 /\
  spar_agR sp > 0 /\
  plan_regular (bld_e0x b) (bld_e0y b) (bld_rx b) (bld_ry b) (bld_ls b)
    (bld_compactness b) /\
  elevation_regular (bld_masses b) (bld_stiffnesses_x b)
    (bld_plan_areas b) /\
  elevation_regular (bld_masses b) (bld_stiffnesses_y b)
    (bld_plan_areas b) /\
  bld_T1_x b <= 4 * sp_TC (spar_sp sp) /\
  bld_T1_y b <= 4 * sp_TC (spar_sp sp) /\
  all_drifts_ok (spar_ic sp) (spar_ns_cat sp) sds_x /\
  all_drifts_ok (spar_ic sp) (spar_ns_cat sp) sds_y /\
  all_pdelta_ok (pdelta_theta_max (spar_pda sp)) sds_x /\
  all_pdelta_ok (pdelta_theta_max (spar_pda sp)) sds_y.

(* ================================================================ *)
(*  DECIDABILITY — item 28                                           *)
(* ================================================================ *)

Lemma plan_regular_dec : forall e0x e0y rx ry ls compactness,
  { plan_regular e0x e0y rx ry ls compactness } +
  { ~ plan_regular e0x e0y rx ry ls compactness }.
Proof.
  intros. unfold plan_regular.
  destruct (Rge_dec compactness (19/20));
  destruct (Rle_dec (Rabs e0x) (3/10 * rx));
  destruct (Rle_dec (Rabs e0y) (3/10 * ry));
  destruct (Rge_dec rx ls);
  destruct (Rge_dec ry ls);
  try (left; tauto); right; tauto.
Defined.

Lemma all_drifts_ok_dec : forall ic cat sds,
  { all_drifts_ok ic cat sds } + { ~ all_drifts_ok ic cat sds }.
Proof.
  intros ic cat sds. induction sds as [|sd rest IH]; simpl.
  - left. exact I.
  - destruct (drift_ok_dec ic cat (sd_dr sd) (sd_h sd));
    destruct IH; try (left; tauto); right; tauto.
Defined.

Lemma all_pdelta_ok_dec : forall theta_max sds,
  { all_pdelta_ok theta_max sds } + { ~ all_pdelta_ok theta_max sds }.
Proof.
  intros theta_max sds. induction sds as [|sd rest IH]; simpl.
  - left. exact I.
  - destruct (Rle_dec (sd_theta sd) theta_max);
    destruct IH; try (left; tauto); right; tauto.
Defined.

(* Helper: decidability for mass_ratio_ok.                           *)
Lemma mass_ratio_ok_dec : forall m1 m2,
  { mass_ratio_ok m1 m2 } + { ~ mass_ratio_ok m1 m2 }.
Proof.
  intros. unfold mass_ratio_ok.
  destruct (Rle_dec m2 (3/2 * m1));
  destruct (Rle_dec m1 (3/2 * m2));
  try (left; tauto); right; tauto.
Defined.

Lemma stiffness_continuity_dec : forall k1 k2,
  { stiffness_continuity k1 k2 } + { ~ stiffness_continuity k1 k2 }.
Proof.
  intros. unfold stiffness_continuity. apply Rge_dec.
Defined.

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
Defined.

Lemma setback_ok_dec : forall a1 a2,
  { setback_ok a1 a2 } + { ~ setback_ok a1 a2 }.
Proof.
  intros. unfold setback_ok. apply Rge_dec.
Defined.

Lemma stiffness_avg3_ok_dec : forall ks,
  { stiffness_avg3_ok ks } + { ~ stiffness_avg3_ok ks }.
Proof.
  intros ks. induction ks as [|k rest IH]; simpl.
  - left. exact I.
  - destruct rest as [|k1 rest1].
    + left. exact I.
    + destruct rest1 as [|k2 rest2].
      * left. exact I.
      * destruct rest2 as [|k3 rest3].
        -- left. exact I.
        -- destruct (Rge_dec k (4/5 * ((k1 + k2 + k3) / 3)));
           destruct IH;
           try (left; tauto); right; tauto.
Defined.

Lemma elevation_regular_dec : forall masses stiffnesses plan_areas,
  { elevation_regular masses stiffnesses plan_areas } +
  { ~ elevation_regular masses stiffnesses plan_areas }.
Proof.
  intros. unfold elevation_regular.
  destruct (all_adjacent_dec mass_ratio_ok mass_ratio_ok_dec masses);
  destruct (all_adjacent_dec stiffness_continuity stiffness_continuity_dec
              stiffnesses);
  destruct (stiffness_avg3_ok_dec stiffnesses);
  destruct (all_adjacent_dec setback_ok setback_ok_dec plan_areas);
  try (left; tauto); right; tauto.
Defined.

Lemma Forall_dec : forall {A : Type} (P : A -> Prop)
    (P_dec : forall x, { P x } + { ~ P x }) (l : list A),
  { Forall P l } + { ~ Forall P l }.
Proof.
  intros A P P_dec l. induction l as [|x rest IH]; simpl.
  - left. constructor.
  - destruct (P_dec x); destruct IH.
    + left. constructor; assumption.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
Defined.

Lemma well_formed_spectrum_dec : forall p,
  { well_formed_spectrum p } + { ~ well_formed_spectrum p }.
Proof.
  intros. unfold well_formed_spectrum.
  destruct (Rgt_dec (sp_S p) 0);
  destruct (Rgt_dec (sp_TB p) 0);
  destruct (Rlt_dec (sp_TB p) (sp_TC p));
  destruct (Rlt_dec (sp_TC p) (sp_TD p));
  try (left; tauto); right; tauto.
Defined.

Lemma strictly_increasing_aux_dec : forall prev l,
  { strictly_increasing_aux prev l } +
  { ~ strictly_increasing_aux prev l }.
Proof.
  intros prev l. revert prev.
  induction l as [|s rest IH]; simpl; intros prev.
  - left. exact I.
  - destruct (Rgt_dec (st_z s) prev);
    destruct (IH (st_z s));
    try (left; tauto); right; tauto.
Defined.

Lemma strictly_increasing_dec : forall l,
  { strictly_increasing l } + { ~ strictly_increasing l }.
Proof.
  intros. unfold strictly_increasing.
  apply strictly_increasing_aux_dec.
Defined.

Lemma well_formed_building_dec : forall b,
  { well_formed_building b } + { ~ well_formed_building b }.
Proof.
  intros. unfold well_formed_building.
  destruct (Nat.eq_dec (length (bld_stiffnesses_x b)) (length (bld_storeys b)));
  destruct (Nat.eq_dec (length (bld_stiffnesses_y b)) (length (bld_storeys b)));
  destruct (Nat.eq_dec (length (bld_weights b)) (length (bld_storeys b)));
  destruct (Nat.eq_dec (length (bld_plan_areas b)) (length (bld_storeys b)));
  destruct (strictly_increasing_dec (bld_storeys b));
  destruct (Forall_dec (fun s => st_m s > 0) (fun s => Rgt_dec (st_m s) 0)
              (bld_storeys b));
  destruct (Forall_dec (fun k => k > 0) (fun k => Rgt_dec k 0)
              (bld_stiffnesses_x b));
  destruct (Forall_dec (fun k => k > 0) (fun k => Rgt_dec k 0)
              (bld_stiffnesses_y b));
  destruct (Forall_dec (fun w => w > 0) (fun w => Rgt_dec w 0)
              (bld_weights b));
  destruct (Forall_dec (fun a => a > 0) (fun a => Rgt_dec a 0)
              (bld_plan_areas b));
  destruct (Rgt_dec (bld_T1_x b) 0);
  destruct (Rgt_dec (bld_T1_y b) 0);
  destruct (Rge_dec (bld_au_a1 b) 1);
  try (left; tauto); right; tauto.
Defined.

Theorem ec8_compliant_dec : forall b sp,
  { ec8_compliant b sp } + { ~ ec8_compliant b sp }.
Proof.
  intros. unfold ec8_compliant.
  set (sds_x := compute_storey_data b sp (bld_stiffnesses_x b) (bld_T1_x b)).
  set (sds_y := compute_storey_data b sp (bld_stiffnesses_y b) (bld_T1_y b)).
  destruct (well_formed_building_dec b);
  destruct (well_formed_spectrum_dec (spar_sp sp));
  destruct (Req_EM_T (spar_q sp) (q0 (bld_dc b) (bld_ss b) (bld_au_a1 b)));
  destruct (Rge_dec (spar_xi sp) 0);
  destruct (Rgt_dec (spar_agR sp) 0);
  destruct (plan_regular_dec (bld_e0x b) (bld_e0y b)
              (bld_rx b) (bld_ry b) (bld_ls b) (bld_compactness b));
  destruct (elevation_regular_dec (bld_masses b) (bld_stiffnesses_x b)
              (bld_plan_areas b));
  destruct (elevation_regular_dec (bld_masses b) (bld_stiffnesses_y b)
              (bld_plan_areas b));
  destruct (Rle_dec (bld_T1_x b) (4 * sp_TC (spar_sp sp)));
  destruct (Rle_dec (bld_T1_y b) (4 * sp_TC (spar_sp sp)));
  destruct (all_drifts_ok_dec (spar_ic sp) (spar_ns_cat sp) sds_x);
  destruct (all_drifts_ok_dec (spar_ic sp) (spar_ns_cat sp) sds_y);
  destruct (all_pdelta_ok_dec (pdelta_theta_max (spar_pda sp)) sds_x);
  destruct (all_pdelta_ok_dec (pdelta_theta_max (spar_pda sp)) sds_y);
  try (left; tauto); right; tauto.
Defined.

(* ================================================================ *)
(*  EXTRACTION — item 29                                             *)
(* ================================================================ *)

Require Import ExtrOcamlBasic ExtrOcamlNatInt.

(* Map Coq reals to OCaml floats for executable extraction.          *)
(* WARNING: All proofs hold over mathematical reals (R), not IEEE    *)
(* 754 floats.  Rounding, NaN, ±infinity, and denormals can violate  *)
(* any proved property at the executable level.  For sound execution, *)
(* use interval arithmetic or verify floating-point error bounds     *)
(* separately (e.g. via Flocq).                                      *)
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant Rplus => "( +. )".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Rminus => "( -. )".
Extract Inlined Constant Rdiv => "(fun a b -> a /. b)".
Extract Inlined Constant Rinv => "(fun x -> 1.0 /. x)".
Extract Inlined Constant Rle_dec => "(fun a b -> if a <= b then true else false)".
Extract Inlined Constant Rge_dec => "(fun a b -> if a >= b then true else false)".
Extract Inlined Constant Ropp => "(fun x -> ~-. x)".
Extract Inlined Constant Rabs => "(fun x -> Float.abs x)".
Extract Inlined Constant Rmax => "(fun a b -> if a >= b then a else b)".
Extract Inlined Constant Rgt_dec => "(fun a b -> if a > b then true else false)".
Extract Inlined Constant Rlt_dec => "(fun a b -> if a < b then true else false)".
Extract Inlined Constant Req_EM_T => "(fun a b -> if a = b then true else false)".
Extract Inlined Constant sqrt => "sqrt".
Extract Inlined Constant ClassicalDedekindReals.sig_forall_dec => "(fun _ -> None)".

Set Extraction Output Directory ".".

Extraction "eurocode8.ml"
  ec8_compliant_dec compute_storey_data
  Se Sd Sve Fb Fi
  combine_srss combine_30pct
  storey_forces storey_shears storey_heights storey_gravities storey_drifts
  spectrum_lookup gamma_I q0
  compute_eta
  torsion_amplification
  classify_pdelta pdelta_amplification pdelta_theta_max
  drift_limit nu lambda.
