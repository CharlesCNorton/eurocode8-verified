# eurocode8-verified — roadmap

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
