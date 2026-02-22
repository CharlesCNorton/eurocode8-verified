# eurocode8-verified — roadmap

1. Add an epsilon-tolerant float comparison utility for extracted-code validation (structural float equality via `Req_EM_T` is fragile under different arithmetic evaluation paths)
2. Convert test_eurocode8.ml to assertion-based checks that fail on mismatch, not just print expected vs actual
3. Add failing test cases for each individual compliance check (eccentricity violation, drift violation, P-delta violation, mass ratio violation, stiffness discontinuity, q mismatch, bad storey data) to confirm the checker correctly rejects non-compliant inputs
4. Add a test case documenting the float equality fragility in ec8_compliant_dec (demonstrate that computing spar_q via a different arithmetic path than `q0` can cause spurious compliance failure due to IEEE 754 non-associativity)

5. Parameterize the P-delta compliance threshold in ec8_compliant (currently hardcoded to θ ≤ 0.20, which excludes the PD_Detailed regime 0.20 < θ ≤ 0.30 that the standard permits with explicit second-order analysis; add an analysis-type flag or parameterize theta_max)
6. Encode the storey height convention in types (st_z is cumulative height from base, not individual storey height; storey_data_consistent_aux starts from prev_z = 0 and requires sd_h = st_z - prev_z, so a user who provides st_z as storey height gets a silent consistency failure; add a well-formedness constraint requiring strictly increasing st_z values)
7. Prove actual continuity of Se on [0, ∞) by composing branch continuity with branch agreement at corner periods
8. Compute storey_data (dr, h, θ) from building model and seismic parameters inside ec8_compliant instead of taking them as exogenous input
9. Define η computation: η = max(√(10/(5+ξ)), 0.55) instead of taking η as a parameter
10. Add direction-dependent properties to building model (separate T1, stiffnesses, drifts for x and y directions)

11. Add compactness check to plan_regular (clause 4.2.3.2: approximately convex plan shape)
12. Add setback constraints to elevation_regular (clause 4.2.3.3)
13. Add 80%-of-average-of-three-storeys-above rule to stiffness_continuity (clause 4.2.3.3)
14. Add vertical seismic action spectrum (clause 4.3.3.5.2)
15. Add accidental torsion amplification (clause 4.3.3.2.4: multiply by 1 + 0.6·x/Le)
16. Add combination of seismic components (clause 4.3.3.5.1: √(Ex² + Ey²) or 100%+30% rules)
17. Add modal response spectrum analysis (clause 4.3.3.3)
18. Add capacity design rules (clause 5.2.3+)
19. Add site-specific spectrum support (clause 3.2.2.3)
20. Add near-fault directivity provisions
