# eurocode8-verified — roadmap

1. Parameterize the P-delta compliance threshold in ec8_compliant (currently hardcoded to θ ≤ 0.20, which excludes the PD_Detailed regime 0.20 < θ ≤ 0.30 that the standard permits with explicit second-order analysis; add an analysis-type flag or parameterize theta_max)
2. Encode the storey height convention in types (st_z is cumulative height from base, not individual storey height; storey_data_consistent_aux starts from prev_z = 0 and requires sd_h = st_z - prev_z, so a user who provides st_z as storey height gets a silent consistency failure; add a well-formedness constraint requiring strictly increasing st_z values)
3. Prove actual continuity of Se on [0, ∞) by composing branch continuity with branch agreement at corner periods
4. Compute storey_data (dr, h, θ) from building model and seismic parameters inside ec8_compliant instead of taking them as exogenous input
5. Define η computation: η = max(√(10/(5+ξ)), 0.55) instead of taking η as a parameter
6. Add direction-dependent properties to building model (separate T1, stiffnesses, drifts for x and y directions)

7. Add compactness check to plan_regular (clause 4.2.3.2: approximately convex plan shape)
8. Add setback constraints to elevation_regular (clause 4.2.3.3)
9. Add 80%-of-average-of-three-storeys-above rule to stiffness_continuity (clause 4.2.3.3)
10. Add vertical seismic action spectrum (clause 4.3.3.5.2)
11. Add accidental torsion amplification (clause 4.3.3.2.4: multiply by 1 + 0.6·x/Le)
12. Add combination of seismic components (clause 4.3.3.5.1: √(Ex² + Ey²) or 100%+30% rules)
13. Add modal response spectrum analysis (clause 4.3.3.3)
14. Add capacity design rules (clause 5.2.3+)
15. Add site-specific spectrum support (clause 3.2.2.3)
16. Add near-fault directivity provisions
