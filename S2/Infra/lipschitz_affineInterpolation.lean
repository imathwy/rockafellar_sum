module

public import ReasLib.Analysis.AffineInterpolation

public section

universe u

/- Infrastructure E.3 (Lipschitz bound for affine interpolation) (1).
The affine interpolation from `u` at time `a` to `v` at time `b` is
`K`-Lipschitz on `Set.Icc a b` under the corresponding endpoint bound. -/
#check (AffineMap.lipschitzOnWith_lineMap_interval :
  ∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {u v : E} {K : NNReal},
    a < b → ‖v - u‖ ≤ (K : ℝ) * (b - a) →
      LipschitzOnWith K
        (fun t : ℝ ↦ AffineMap.lineMap u v ((t - a) / (b - a))) (Set.Icc a b))

/- Infrastructure E.3 (Lipschitz bound for affine interpolation) (2).
The affine interpolation from `u` to `v` remains in any convex set containing
both endpoints throughout `Set.Icc a b`. -/
#check (Convex.mapsTo_lineMap_interval :
  ∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {u v : E} {C : Set E},
    a < b → Convex ℝ C → u ∈ C → v ∈ C →
      Set.MapsTo
        (fun t : ℝ ↦ AffineMap.lineMap u v ((t - a) / (b - a))) (Set.Icc a b) C)
