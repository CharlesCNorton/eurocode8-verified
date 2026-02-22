# eurocode8-verified — roadmap

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
