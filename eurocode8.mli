
type __ = Obj.t

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val pred : int -> int

val add : int -> int -> int

val mul : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val pow : int -> int -> int
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val size_nat : positive -> int

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_nat : int -> positive

  val of_succ_nat : int -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)
 end

val z_lt_dec : z -> z -> bool

val z_lt_ge_dec : z -> z -> bool

val z_lt_le_dec : z -> z -> bool

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qlt_le_dec : q -> q -> bool

val qarchimedean : q -> positive

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val qabs : q -> q

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

val z_inj_nat_rev : int -> z

type cReal = { seq : (z -> q); scale : z }

type cRealLt = z

val cRealLt_lpo_dec :
  cReal -> cReal -> (__ -> (int -> bool) -> int option) -> (cRealLt, __) sum

val sig_forall_dec : (int -> bool) -> int option

val lowerCutBelow : (q -> bool) -> q

val lowerCutAbove : (q -> bool) -> q

type dReal = (q -> bool)

val dRealQlim_rec : (q -> bool) -> int -> int -> q

val dRealAbstr : cReal -> dReal

val dRealQlim : dReal -> int -> q

val dRealQlimExp2 : dReal -> int -> q

val cReal_of_DReal_seq : dReal -> z -> q

val cReal_of_DReal_scale : dReal -> z

val dRealRepr : dReal -> cReal

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val iPR_2 : positive -> float

val iPR : positive -> float

val iZR : z -> float

val total_order_T : float -> float -> bool option

module type RinvSig =
 sig
  val coq_Rinv : float -> float
 end

module RinvImpl :
 RinvSig



val req_dec_T : float -> float -> bool

val rlt_dec : float -> float -> bool

val rgt_dec : float -> float -> bool



type ground_type =
| GroundA
| GroundB
| GroundC
| GroundD
| GroundE

type spectrum_type =
| Type1
| Type2

type importance_class =
| ClassI
| ClassII
| ClassIII
| ClassIV

val gamma_I : importance_class -> float

type spectrum_params = { sp_S : float; sp_TB : float; sp_TC : float;
                         sp_TD : float }

val spectrum_lookup : spectrum_type -> ground_type -> spectrum_params

val se : spectrum_params -> float -> float -> float -> float

type ductility_class =
| DCL
| DCM
| DCH

type structural_system =
| FrameSystem
| DualFrameEquiv
| DualWallEquiv
| DuctileWallSystem
| InvertedPendulum
| TorsionallyFlexible

val q0 : ductility_class -> structural_system -> float -> float

val beta : float

val sd : spectrum_params -> float -> float -> float -> float -> float

val lambda : float -> spectrum_params -> int -> float

val fb : float -> float -> float -> float

type storey = { st_z : float; st_m : float }

val sum_zm : storey list -> float

val fi : float -> storey -> float -> float

val storey_forces : float -> storey list -> float list

type ns_category =
| NS_Brittle
| NS_Ductile
| NS_None

val drift_limit : ns_category -> float

val nu : importance_class -> float

val drift_ok_dec : importance_class -> ns_category -> float -> float -> bool

val theta : float -> float -> float -> float -> float

type pdelta_regime =
| PD_Negligible
| PD_Approximate
| PD_Detailed
| PD_Inadmissible

val classify_pdelta : float -> pdelta_regime

val pdelta_amplification : float -> float

type building = { bld_storeys : storey list; bld_stiffnesses : float list;
                  bld_T1 : float; bld_dc : ductility_class;
                  bld_ss : structural_system; bld_au_a1 : float;
                  bld_e0x : float; bld_e0y : float; bld_rx : float;
                  bld_ry : float; bld_ls : float }

val bld_masses : building -> float list

type seismic_params = { spar_ic : importance_class;
                        spar_sp : spectrum_params; spar_agR : float;
                        spar_eta : float; spar_q : float;
                        spar_ns_cat : ns_category }

type storey_data = { sd_dr : float; sd_h : float; sd_Ptot : float;
                     sd_Vtot : float }

val sd_theta : storey_data -> float

val storey_data_consistent_dec : storey list -> storey_data list -> bool

val plan_regular_dec : float -> float -> float -> float -> float -> bool

val all_drifts_ok_dec :
  importance_class -> ns_category -> storey_data list -> bool

val all_pdelta_ok_dec : storey_data list -> bool

val mass_ratio_ok_dec : float -> float -> bool

val stiffness_continuity_dec : float -> float -> bool

val all_adjacent_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

val elevation_regular_dec : float list -> float list -> bool

val ec8_compliant_dec : building -> seismic_params -> storey_data list -> bool
