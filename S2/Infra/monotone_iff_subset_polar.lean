module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone

public section

universe u v

/- Infrastructure D.3 (Monotonicity as inclusion in the polar): a graph is monotone
if and only if it is contained in its monotone polar. -/
#check (DualPairing.isMonotone_iff_subset_polar :
  ∀ {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]
    (P : DualPairing X Xstar) (S : Set (X × Xstar)),
    P.IsMonotone S ↔ S ⊆ P.monotonePolar S)
