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

31. Change all 9 decidability lemmas from Qed to Defined (drift_ok_dec, plan_regular_dec, all_drifts_ok_dec, all_pdelta_ok_dec, mass_ratio_ok_dec, stiffness_continuity_dec, all_adjacent_dec, elevation_regular_dec, ec8_compliant_dec)
32. Add Set Extraction Output Directory to project directory before Extraction command
33. Fix plan_regular to use Rabs on e0x and e0y (standard requires |e0| ≤ 0.30·r, not e0 ≤ 0.30·r)
34. Fix plan_regular_dec to handle Rabs-based eccentricity check
35. Make ν a function of importance class per Table 4.1 instead of a hardcoded constant
36. Fix drift_ok and drift_ok_dec to use importance-class-dependent ν
37. Tighten all_pdelta_ok threshold from 0.30 to 0.20, or parameterize by analysis method (simplified vs second-order)
38. Add importance_class field to seismic_params and wire γI into design ground acceleration (ag = γI × agR)
39. Add ductility_class and structural_system fields to building record
40. Add well_formed_spectrum predicate: sp_TB > 0 ∧ sp_TB < sp_TC ∧ sp_TC < sp_TD
41. Prove spectrum_lookup always produces well_formed_spectrum (case analysis on all 10 entries)
42. Add well_formed_building predicate: length consistency between bld_storeys, bld_masses, bld_stiffnesses, bld_n_storeys; non-negative masses and heights
43. Remove redundant bld_masses field (derive from bld_storeys[].st_m)
44. Remove redundant bld_n_storeys field (derive from length bld_storeys)
45. Link theta function to storey_data.sd_theta via a consistency lemma or eliminate the redundancy
46. Remove dead definition ds (displacement amplification, line 473, never used)
47. Constrain spar_q in ec8_compliant to equal q0 applied to the building's ductility class, structural system, and αu/α1
48. Add consistency check between bld_storeys heights and storey_data heights
49. Compute storey_data (dr, h, θ) from building model and seismic parameters inside ec8_compliant instead of taking them as exogenous input
50. Prove Se_nonneg: Se(T) ≥ 0 when ag ≥ 0, S ≥ 0, eta ≥ 0, T ≥ 0
51. Prove q0_ge_1 for all valid (ductility class, system type, αu/α1 ≥ 1) combinations
52. Prove spectrum_lookup produces well-ordered parameters (TB < TC < TD, all positive)
53. Prove lambda always returns exactly 17/20 or 1
54. Prove pdelta_amplification monotone increasing in theta
55. Prove full drift ordering: None ≥ Ductile ≥ Brittle
56. Prove end-to-end: spectrum_lookup → Se → Sd → Fb → Fi composition lemma
57. Add lower bound check on η (η ≥ 0.55 per clause 3.2.2.2)
58. Prove q0 range bounds for valid αu/α1 inputs
59. Rename Se_continuous_at_TC and Se_continuous_at_TD to Se_branch_agreement_at_TC and Se_branch_agreement_at_TD (they prove branch consistency, not ε-δ continuity)
60. Prove actual continuity of Se on [0, ∞) by composing branch continuity with branch agreement, or document the distinction explicitly
61. Add compactness check to plan_regular (clause 4.2.3.2: approximately convex plan shape)
62. Add setback constraints to elevation_regular (clause 4.2.3.3)
63. Add 80%-of-average-of-three-storeys-above rule to stiffness_continuity (clause 4.2.3.3)
64. Document list ordering convention for stiffness_continuity (ground floor first or top floor first)
65. Add non-negative period guard to Se (reject T < 0 or require T ≥ 0 as precondition)
66. Define η computation: η = √(10/(5+ξ)) with floor at 0.55
67. Add direction-dependent properties to building model (separate T1, stiffnesses, drifts for x and y)
68. Remove sum_Fi_eq_Fb from Extraction command (Prop-level proof, extracts to __)
69. Simplify Rge_dec extraction from redundant nested conditional to plain comparison
70. Investigate pruning dead constructive-reals infrastructure (~500 lines) from extracted OCaml
71. Add assertion-based checks to test_eurocode8.ml (fail on mismatch, not just print)
72. Add epsilon-tolerant float comparison for extracted-code validation
73. Add failing test cases for each individual check (eccentricity, drift, P-delta, mass ratio, stiffness) to confirm rejection
74. Add _CoqProject file
75. Add Makefile or dune-project for Coq compilation and OCaml build
76. Add .gitignore for .vo, .vok, .vos, .glob, .aux, .cmi, .cmo, .cmx
77. Add LICENSE file (MIT text)
78. Add vertical seismic action spectrum (clause 4.3.3.5.2)
79. Add accidental torsion amplification (clause 4.3.3.2.4: multiply by 1 + 0.6·x/Le)
80. Add combination of seismic components (clause 4.3.3.5.1: √(Ex² + Ey²) or 100%+30% rules)
81. Add modal response spectrum analysis (clause 4.3.3.3)
82. Add capacity design rules (clause 5.2.3+)
83. Add site-specific spectrum support (clause 3.2.2.3)
84. Add near-fault directivity provisions
