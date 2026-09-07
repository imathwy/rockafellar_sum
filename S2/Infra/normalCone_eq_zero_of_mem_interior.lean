module

public import ReasLib.Analysis.Convex.NormalCone

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.8 (Normal cone at an interior point): the normal cone of a set at
an interior point is the singleton containing zero. -/
#check (DualPairing.normalCone_eq_zero_of_mem_interior :
  ∀ (P : DualPairing X Xstar) {C : Set X} {x : X},
    x ∈ interior C → P.normalCone C x = {0})

end DualPairing
