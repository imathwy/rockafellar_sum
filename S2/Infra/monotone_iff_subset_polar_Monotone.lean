module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

#check (DualPairing.IsMonotone :
  DualPairing X Xstar → Set (X × Xstar) → Prop)

#check (DualPairing.IsMonotone.mono :
  ∀ (P : DualPairing X Xstar) {S T : Set (X × Xstar)},
    T ⊆ S → P.IsMonotone S → P.IsMonotone T)
