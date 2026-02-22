# eurocode8-verified — roadmap

## Done

1. Define ground types A–E as inductive type with parameter table (S, TB, TC, TD) per Table 3.2/3.3
2. Define importance classes I–IV with γI factors
3. Define elastic response spectrum Se(T) as piecewise function over four segments
4. Prove Se continuous at corner periods TB, TC, TD
5. Prove Se monotone increasing on [0, TB], plateau on [TB, TC], decreasing on [TC, TD] and [TD, ∞)
6. Define ductility classes DCL/DCM/DCH and structural system types as inductive types
7. Define behavior factor q as function of (ductility class × system type) per Table 5.1
8. Define design spectrum Sd(T) = Se(T)/q with floor at β·ag
9. Prove Sd(T) ≥ β·ag for all T and valid (ductility class, system type) pairs
10. Prove Sd(T) ≤ Se(T) for all T
11. Define lateral force method applicability predicate: T1 ≤ 4·TC ∧ elevation-regular
12. Define base shear Fb = Sd(T1)·m·λ with λ selection rule
13. Define storey force distribution Fi = Fb·(zi·mi)/Σ(zj·mj)
14. Prove ΣFi = Fb
15. Prove Fi > 0 for all storeys with positive mass
16. Define displacement amplification ds = q·de
17. Define three drift limit categories (brittle/ductile/none) with ν reduction
18. Define drift check as decidable predicate over storey model
19. Prove drift check strictly more permissive for ductile than brittle non-structural
20. Define θ = Ptot·dr/(Vtot·h) per storey
21. Define four P-Δ regimes with boundaries at 0.10, 0.20, 0.30
22. Prove amplification factor 1/(1−θ) bounded in [1.0, 1.25] for θ ∈ (0.10, 0.20]
23. Prove θ > 0.30 implies amplification exceeds 1.43
24. Define plan regularity predicate: compactness, eccentricity ≤ 0.30·r, torsional radius ≥ ls
25. Define elevation regularity predicate: stiffness continuity, mass ratio ≤ 150%, setback constraints
26. Prove plan-regular ∧ elevation-regular → lateral force method applicable
27. Define full compliance predicate composing all checks
28. Prove compliance predicate decidable
29. Extract to executable OCaml
30. Validate extracted checker against standard's worked example
31. Change all 9 decidability lemmas from Qed to Defined
32. Add Set Extraction Output Directory to project directory before Extraction command
33. Fix plan_regular to use Rabs on e0x and e0y
34. Fix plan_regular_dec to handle Rabs-based eccentricity check
35. Make ν a function of importance class per Table 4.1
36. Fix drift_ok and drift_ok_dec to use importance-class-dependent ν
37. Parameterize all_pdelta_ok by theta_max (simplified vs second-order)
38. Add importance_class field to seismic_params and wire γI into design ground acceleration
39. Add ductility_class and structural_system fields to building record
40. Add well_formed_spectrum predicate and prove spectrum_lookup always produces one
41. Add well_formed_building predicate
42. Remove redundant bld_masses field (derive from bld_storeys)
43. Remove redundant bld_n_storeys field (derive from length bld_storeys)
44. Link theta function to storey_data via derived function
45. Constrain spar_q in ec8_compliant to equal q0
46. Add consistency check between bld_storeys heights and storey_data heights
47. Prove Se_nonneg, q0_ge_1, q0_upper, lambda_values, pdelta_amp_increasing, drift ordering, pipeline_valid
48. Rename Se_continuous lemmas to Se_branch_agreement
49. Add lower bound check on η (η ≥ 0.55) in compliance predicate
50. Enforce well_formed_building and well_formed_spectrum in ec8_compliant_dec
51. Enforce agR > 0 in compliance predicate
52. Document T ≥ 0 precondition on Se (guarded by well_formed_building)
53. Document float extraction unsoundness
54. Add extraction directives for Rgt_dec, Rlt_dec, Req_EM_T
55. Realize sig_forall_dec axiom as lazy function
56. Remove stale .mli (interface mismatch with inlined R=float)
57. Rewrite test_eurocode8.ml to match current extracted types
58. Add _CoqProject, Makefile, .gitignore, LICENSE

## Open

1. Compute storey_data (dr, h, θ) from building model and seismic parameters inside ec8_compliant instead of taking them as exogenous input
2. Prove actual continuity of Se on [0, ∞) by composing branch continuity with branch agreement, or document the distinction explicitly
3. Add compactness check to plan_regular (clause 4.2.3.2: approximately convex plan shape)
4. Add setback constraints to elevation_regular (clause 4.2.3.3)
5. Add 80%-of-average-of-three-storeys-above rule to stiffness_continuity (clause 4.2.3.3)
6. Document list ordering convention for stiffness_continuity (ground floor first or top floor first)
7. Define η computation: η = √(10/(5+ξ)) with floor at 0.55
8. Add direction-dependent properties to building model (separate T1, stiffnesses, drifts for x and y)
9. Prune dead constructive-reals infrastructure (~500 lines) from extracted OCaml
10. Add assertion-based checks to test_eurocode8.ml (fail on mismatch, not just print)
11. Add epsilon-tolerant float comparison for extracted-code validation
12. Add failing test cases for each individual check (eccentricity, drift, P-delta, mass ratio, stiffness) to confirm rejection
13. Add vertical seismic action spectrum (clause 4.3.3.5.2)
14. Add accidental torsion amplification (clause 4.3.3.2.4: multiply by 1 + 0.6·x/Le)
15. Add combination of seismic components (clause 4.3.3.5.1: √(Ex² + Ey²) or 100%+30% rules)
16. Add modal response spectrum analysis (clause 4.3.3.3)
17. Add capacity design rules (clause 5.2.3+)
18. Add site-specific spectrum support (clause 3.2.2.3)
19. Add near-fault directivity provisions
