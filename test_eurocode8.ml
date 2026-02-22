open Eurocode8

(* Realize the classical axiom — bounded search up to 1000. *)
let () =
  (* sig_forall_dec is referenced but unused in our float-extracted code *)
  ()

let () =
  (* Type 1 spectrum, Ground type A: S=1.0, TB=0.15, TC=0.4, TD=2.0 *)
  let sp = spectrum_lookup Type1 GroundA in
  Printf.printf "=== Eurocode 8 Verified Checker — Validation ===\n\n";
  Printf.printf "Ground A, Type 1: S=%.2f TB=%.3f TC=%.2f TD=%.1f\n"
    sp.sp_S sp.sp_TB sp.sp_TC sp.sp_TD;

  let ag = 0.25 in
  let eta = 1.0 in
  Printf.printf "\n--- Elastic Response Spectrum Se(T) ---\n";
  Printf.printf "ag = %.2f, eta = %.2f\n" ag eta;
  let se0 = se sp ag eta 0.0 in
  let se_tb = se sp ag eta sp.sp_TB in
  let se_tc = se sp ag eta sp.sp_TC in
  let se_1 = se sp ag eta 1.0 in
  let se_3 = se sp ag eta 3.0 in
  Printf.printf "Se(0)    = %.4f  (expect %.4f = ag*S)\n" se0 (ag *. sp.sp_S);
  Printf.printf "Se(TB)   = %.4f  (expect %.4f = ag*S*eta*2.5)\n"
    se_tb (ag *. sp.sp_S *. eta *. 2.5);
  Printf.printf "Se(TC)   = %.4f  (expect %.4f = plateau)\n"
    se_tc (ag *. sp.sp_S *. eta *. 2.5);
  Printf.printf "Se(1.0)  = %.4f  (expect %.4f = plateau*TC/T)\n"
    se_1 (ag *. sp.sp_S *. eta *. 2.5 *. sp.sp_TC /. 1.0);
  Printf.printf "Se(3.0)  = %.4f  (expect %.4f = plateau*TC*TD/T^2)\n"
    se_3 (ag *. sp.sp_S *. eta *. 2.5 *. sp.sp_TC *. sp.sp_TD /. (3.0 *. 3.0));

  (* Design spectrum *)
  let q_val = 3.0 in
  Printf.printf "\n--- Design Spectrum Sd(T), q=%.1f ---\n" q_val;
  Printf.printf "Sd(0.5)  = %.4f\n" (sd sp ag eta q_val 0.5);
  Printf.printf "beta*ag  = %.4f  (floor)\n" (beta *. ag);

  (* Building model *)
  Printf.printf "\n--- 3-Storey Building Model ---\n";
  let building = {
    bld_storeys = [
      { st_z = 3.0; st_m = 100.0 };
      { st_z = 6.0; st_m = 100.0 };
      { st_z = 9.0; st_m = 80.0 }
    ];
    bld_masses = [100.0; 100.0; 80.0];
    bld_stiffnesses = [1000.0; 900.0; 800.0];
    bld_T1 = 0.5;
    bld_n_storeys = 3;
    bld_e0x = 0.1;
    bld_e0y = 0.1;
    bld_rx = 2.0;
    bld_ry = 2.0;
    bld_ls = 1.5;
  } in

  let seismic = {
    spar_sp = sp;
    spar_ag = ag;
    spar_eta = eta;
    spar_q = q_val;
    spar_ns_cat = NS_Ductile;
  } in

  (* Storey forces *)
  let sd_T1 = sd sp ag eta q_val building.bld_T1 in
  let m_total = 280.0 in
  let lam = lambda building.bld_T1 sp 3 in
  let base_shear = fb sd_T1 m_total lam in
  Printf.printf "Sd(T1=%.2f)  = %.4f\n" building.bld_T1 sd_T1;
  Printf.printf "lambda       = %.4f\n" lam;
  Printf.printf "Fb           = %.4f\n" base_shear;
  let forces = storey_forces base_shear building.bld_storeys in
  List.iteri (fun i f ->
    Printf.printf "  F%d = %.4f\n" (i+1) f
  ) forces;
  let sum_f = List.fold_left ( +. ) 0.0 forces in
  Printf.printf "Sum(Fi)      = %.4f  (expect Fb = %.4f)\n" sum_f base_shear;

  (* P-Delta *)
  Printf.printf "\n--- P-Delta Classification ---\n";
  let show_pd th =
    let regime = match classify_pdelta th with
      | PD_Negligible -> "Negligible"
      | PD_Approximate -> "Approximate"
      | PD_Detailed -> "Detailed"
      | PD_Inadmissible -> "Inadmissible" in
    Printf.printf "theta=%.2f -> %s\n" th regime in
  show_pd 0.05;
  show_pd 0.15;
  show_pd 0.25;
  show_pd 0.35;

  (* Compliance check *)
  Printf.printf "\n--- Compliance Check ---\n";
  let storey_checks = [
    { sd_dr = 0.005; sd_h = 3.0; sd_theta = 0.08 };
    { sd_dr = 0.004; sd_h = 3.0; sd_theta = 0.06 };
    { sd_dr = 0.003; sd_h = 3.0; sd_theta = 0.04 };
  ] in
  let result = ec8_compliant_dec building seismic storey_checks in
  Printf.printf "Result: %s\n" (if result then "COMPLIANT" else "NON-COMPLIANT");

  (* Failing case: excessive theta *)
  Printf.printf "\n--- Failing Case (excessive P-Delta) ---\n";
  let bad_checks = [
    { sd_dr = 0.005; sd_h = 3.0; sd_theta = 0.35 };
    { sd_dr = 0.004; sd_h = 3.0; sd_theta = 0.06 };
    { sd_dr = 0.003; sd_h = 3.0; sd_theta = 0.04 };
  ] in
  let result2 = ec8_compliant_dec building seismic bad_checks in
  Printf.printf "Result: %s\n" (if result2 then "COMPLIANT" else "NON-COMPLIANT");

  Printf.printf "\n=== Validation complete ===\n"
