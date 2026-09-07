module

public import ReasLib.Analysis.Convex.NormalCone

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.7 (Monotonicity of the normal cone): the normal-cone graph of
every set in a continuous dual pair is monotone. -/
#check (DualPairing.isMonotone_normalConeGraph :
  ∀ (P : DualPairing X Xstar) (C : Set X), P.IsMonotone (P.normalConeGraph C))
