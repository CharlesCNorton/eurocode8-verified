# eurocode8-verified — roadmap

1. Compute storey_data (dr, h, θ) from building model and seismic parameters inside ec8_compliant instead of taking them as exogenous input
2. Define η computation: η = max(√(10/(5+ξ)), 0.55) instead of taking η as a parameter
3. Add direction-dependent properties to building model (separate T1, stiffnesses, drifts for x and y directions)

4. Add compactness check to plan_regular (clause 4.2.3.2: approximately convex plan shape)
5. Add setback constraints to elevation_regular (clause 4.2.3.3)
6. Add 80%-of-average-of-three-storeys-above rule to stiffness_continuity (clause 4.2.3.3)
7. Add vertical seismic action spectrum (clause 4.3.3.5.2)
8. Add accidental torsion amplification (clause 4.3.3.2.4: multiply by 1 + 0.6·x/Le)
9. Add combination of seismic components (clause 4.3.3.5.1: √(Ex² + Ey²) or 100%+30% rules)
10. Add modal response spectrum analysis (clause 4.3.3.3)
11. Add capacity design rules (clause 5.2.3+)
12. Add site-specific spectrum support (clause 3.2.2.3)
13. Add near-fault directivity provisions
