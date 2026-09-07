module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.4 (Maximal monotonicity as equality with the polar): a monotone
graph is maximal among monotone graphs exactly when it equals its monotone polar. -/
#check (DualPairing.maximalMonotone_iff_polar_eq :
  ∀ (P : DualPairing X Xstar) (S : Set (X × Xstar)), P.IsMonotone S →
    (Maximal (P.IsMonotone) S ↔ P.monotonePolar S = S))
