open Eurocode8

let eps = 1e-10
let pass = ref 0
let fail = ref 0

let assert_float_eq label expected actual =
  if Float.abs (expected -. actual) > eps then begin
    Printf.eprintf "FAIL: %s: expected %.10f, got %.10f (diff %.2e)\n"
      label expected actual (Float.abs (expected -. actual));
    incr fail
  end else
    incr pass

let assert_bool label expected actual =
  if expected <> actual then begin
    Printf.eprintf "FAIL: %s: expected %b, got %b\n" label expected actual;
    incr fail
  end else
    incr pass

let assert_pdelta label expected actual =
  let eq = match expected, actual with
    | PD_Negligible, PD_Negligible -> true
    | PD_Approximate, PD_Approximate -> true
    | PD_Detailed, PD_Detailed -> true
    | PD_Inadmissible, PD_Inadmissible -> true
    | _ -> false in
  if not eq then begin
    Printf.eprintf "FAIL: %s: P-delta regime mismatch\n" label;
    incr fail
  end else
    incr pass

let () =
  let sp = spectrum_lookup Type1 GroundA in
  let ag = 0.25 in
  let eta = 1.0 in
  let plateau = ag *. sp.sp_S *. eta *. 2.5 in

  (* Spectrum parameters *)
  assert_float_eq "Ground A S"  1.0  sp.sp_S;
  assert_float_eq "Ground A TB" 0.15 sp.sp_TB;
  assert_float_eq "Ground A TC" 0.4  sp.sp_TC;
  assert_float_eq "Ground A TD" 2.0  sp.sp_TD;

  (* Elastic response spectrum *)
  assert_float_eq "Se(0)"   (ag *. sp.sp_S)  (se sp ag eta 0.0);
  assert_float_eq "Se(TB)"  plateau           (se sp ag eta sp.sp_TB);
  assert_float_eq "Se(TC)"  plateau           (se sp ag eta sp.sp_TC);
  assert_float_eq "Se(1.0)" (plateau *. sp.sp_TC /. 1.0)
    (se sp ag eta 1.0);
  assert_float_eq "Se(3.0)"
    (plateau *. sp.sp_TC *. sp.sp_TD /. (3.0 *. 3.0))
    (se sp ag eta 3.0);

  (* Se guard: negative period returns 0 *)
  assert_float_eq "Se(-1.0)" 0.0 (se sp ag eta (-1.0));

  (* Design spectrum *)
  let q_val = q0 DCM FrameSystem 1.2 in
  assert_float_eq "q0 DCM Frame 1.2" 3.6 q_val;
  assert_float_eq "Sd(0.5)" (plateau *. sp.sp_TC /. 0.5 /. q_val)
    (sd sp ag eta q_val 0.5);
  assert_float_eq "beta" 0.2 beta;

  (* q0 wall system fix: DCM DualWallEquiv uses 3*au_a1 *)
  assert_float_eq "q0 DCM DualWallEquiv 1.2" 3.6 (q0 DCM DualWallEquiv 1.2);
  assert_float_eq "q0 DCM DuctileWall 1.2"   3.6 (q0 DCM DuctileWallSystem 1.2);

  (* Importance factors *)
  assert_float_eq "gamma_I ClassI"   0.8 (gamma_I ClassI);
  assert_float_eq "gamma_I ClassII"  1.0 (gamma_I ClassII);
  assert_float_eq "gamma_I ClassIII" 1.2 (gamma_I ClassIII);
  assert_float_eq "gamma_I ClassIV"  1.4 (gamma_I ClassIV);

  (* Drift limits *)
  assert_float_eq "drift_limit brittle" 0.005   (drift_limit NS_Brittle);
  assert_float_eq "drift_limit ductile" 0.0075  (drift_limit NS_Ductile);
  assert_float_eq "drift_limit none"    0.01    (drift_limit NS_None);

  (* Nu reduction factors *)
  assert_float_eq "nu ClassI"   0.4 (nu ClassI);
  assert_float_eq "nu ClassII"  0.4 (nu ClassII);
  assert_float_eq "nu ClassIII" 0.5 (nu ClassIII);
  assert_float_eq "nu ClassIV"  0.5 (nu ClassIV);

  (* Lambda correction factor *)
  let lam = lambda 0.5 sp 3 in
  assert_float_eq "lambda T1=0.5 n=3" 0.85 lam;
  assert_float_eq "lambda T1=2.0 n=3" 1.0  (lambda 2.0 sp 3);
  assert_float_eq "lambda T1=0.5 n=2" 1.0  (lambda 0.5 sp 2);

  (* P-Delta classification *)
  assert_pdelta "pdelta 0.05" PD_Negligible   (classify_pdelta 0.05);
  assert_pdelta "pdelta 0.15" PD_Approximate  (classify_pdelta 0.15);
  assert_pdelta "pdelta 0.25" PD_Detailed     (classify_pdelta 0.25);
  assert_pdelta "pdelta 0.35" PD_Inadmissible (classify_pdelta 0.35);

  (* P-Delta amplification *)
  assert_float_eq "pdelta_amp 0.15" (1.0 /. 0.85) (pdelta_amplification 0.15);

  (* Building model *)
  let bld = {
    bld_storeys = [
      { st_z = 3.0; st_m = 100.0 };
      { st_z = 6.0; st_m = 100.0 };
      { st_z = 9.0; st_m = 80.0 }
    ];
    bld_stiffnesses = [1000.0; 900.0; 800.0];
    bld_T1 = 0.5;
    bld_dc = DCM;
    bld_ss = FrameSystem;
    bld_au_a1 = 1.2;
    bld_e0x = 0.1;
    bld_e0y = 0.1;
    bld_rx = 2.0;
    bld_ry = 2.0;
    bld_ls = 1.5;
  } in

  let seismic = {
    spar_ic = ClassII;
    spar_sp = sp;
    spar_agR = ag;
    spar_eta = eta;
    spar_q = q_val;
    spar_ns_cat = NS_Ductile;
  } in

  (* Base shear and storey forces *)
  let sd_T1 = sd sp ag eta q_val bld.bld_T1 in
  let m_total = 280.0 in
  let base_shear = fb sd_T1 m_total lam in
  let forces = storey_forces base_shear bld.bld_storeys in
  let sum_f = List.fold_left ( +. ) 0.0 forces in
  assert_float_eq "sum_Fi = Fb" base_shear sum_f;

  (* Compliant building *)
  let storey_checks = [
    { sd_dr = 0.005; sd_h = 3.0; sd_Ptot = 800.0; sd_Vtot = 150.0 };
    { sd_dr = 0.004; sd_h = 3.0; sd_Ptot = 500.0; sd_Vtot = 120.0 };
    { sd_dr = 0.003; sd_h = 3.0; sd_Ptot = 200.0; sd_Vtot = 80.0 };
  ] in
  assert_bool "compliant building" true
    (ec8_compliant_dec bld seismic storey_checks);

  (* Excessive P-delta -> non-compliant *)
  let bad_checks = [
    { sd_dr = 0.020; sd_h = 3.0; sd_Ptot = 8000.0; sd_Vtot = 150.0 };
    { sd_dr = 0.004; sd_h = 3.0; sd_Ptot = 500.0;  sd_Vtot = 120.0 };
    { sd_dr = 0.003; sd_h = 3.0; sd_Ptot = 200.0;  sd_Vtot = 80.0 };
  ] in
  assert_bool "excessive pdelta" false
    (ec8_compliant_dec bld seismic bad_checks);

  (* --- Individual rejection tests --- *)

  (* Eccentricity violation: e0x too large for rx *)
  let bld_ecc = { bld with bld_e0x = 1.0 } in
  assert_bool "reject: eccentricity" false
    (ec8_compliant_dec bld_ecc seismic storey_checks);

  (* Drift violation: excessive interstorey drift *)
  let drift_checks = [
    { sd_dr = 0.100; sd_h = 3.0; sd_Ptot = 800.0; sd_Vtot = 150.0 };
    { sd_dr = 0.004; sd_h = 3.0; sd_Ptot = 500.0; sd_Vtot = 120.0 };
    { sd_dr = 0.003; sd_h = 3.0; sd_Ptot = 200.0; sd_Vtot = 80.0 };
  ] in
  assert_bool "reject: drift" false
    (ec8_compliant_dec bld seismic drift_checks);

  (* P-delta violation: theta > 0.20 *)
  let pdelta_checks = [
    { sd_dr = 0.020; sd_h = 3.0; sd_Ptot = 8000.0; sd_Vtot = 150.0 };
    { sd_dr = 0.004; sd_h = 3.0; sd_Ptot = 500.0;  sd_Vtot = 120.0 };
    { sd_dr = 0.003; sd_h = 3.0; sd_Ptot = 200.0;  sd_Vtot = 80.0 };
  ] in
  assert_bool "reject: pdelta" false
    (ec8_compliant_dec bld seismic pdelta_checks);

  (* Mass ratio violation: adjacent storey mass ratio > 150% *)
  let bld_mass = { bld with bld_storeys = [
    { st_z = 3.0; st_m = 100.0 };
    { st_z = 6.0; st_m = 300.0 };
    { st_z = 9.0; st_m = 80.0 }
  ] } in
  assert_bool "reject: mass ratio" false
    (ec8_compliant_dec bld_mass seismic storey_checks);

  (* Stiffness discontinuity: k drops below 70% of adjacent *)
  let bld_stiff = { bld with bld_stiffnesses = [100.0; 900.0; 800.0] } in
  assert_bool "reject: stiffness" false
    (ec8_compliant_dec bld_stiff seismic storey_checks);

  (* q mismatch: spar_q doesn't match q0 for building's system *)
  let seismic_badq = { seismic with spar_q = 5.0 } in
  assert_bool "reject: q mismatch" false
    (ec8_compliant_dec bld seismic_badq storey_checks);

  (* Bad storey data: height mismatch *)
  let bad_sd = [
    { sd_dr = 0.005; sd_h = 4.0; sd_Ptot = 800.0; sd_Vtot = 150.0 };
    { sd_dr = 0.004; sd_h = 3.0; sd_Ptot = 500.0; sd_Vtot = 120.0 };
    { sd_dr = 0.003; sd_h = 3.0; sd_Ptot = 200.0; sd_Vtot = 80.0 };
  ] in
  assert_bool "reject: storey data" false
    (ec8_compliant_dec bld seismic bad_sd);

  (* Torsional radius violation: rx < ls *)
  let bld_torsion = { bld with bld_rx = 1.0 } in
  assert_bool "reject: torsional radius" false
    (ec8_compliant_dec bld_torsion seismic storey_checks);

  (* Period too long: T1 > 4*TC *)
  let bld_period = { bld with bld_T1 = 2.0 } in
  assert_bool "reject: period" false
    (ec8_compliant_dec bld_period seismic storey_checks);

  (* Float equality fragility: q computed via different arithmetic path *)
  let q_direct = 3.0 *. 1.2 in
  let q_extracted = q0 DCM FrameSystem 1.2 in
  let seismic_direct_q = { seismic with spar_q = q_direct } in
  let structurally_equal = (q_direct = q_extracted) in
  if not structurally_equal then
    (* If IEEE 754 non-associativity breaks equality, the checker rejects *)
    assert_bool "fragility: direct q rejected" false
      (ec8_compliant_dec bld seismic_direct_q storey_checks)
  else
    (* If they happen to be equal, both paths accept *)
    assert_bool "fragility: direct q accepted" true
      (ec8_compliant_dec bld seismic_direct_q storey_checks);

  (* Report *)
  Printf.printf "%d passed, %d failed\n" !pass !fail;
  if !fail > 0 then exit 1
