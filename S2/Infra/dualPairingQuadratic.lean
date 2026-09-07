module

public import ReasLib.FunctionalAnalysis.DualPairing

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.1 (Quadratic pairing on a Banach-dual product) (1) -/
#check (DualPairing.quadratic : DualPairing X Xstar → QuadraticForm ℝ (X × Xstar))
#check (DualPairing.quadratic_apply :
  ∀ (P : DualPairing X Xstar) (x : X) (xstar : Xstar),
    P.quadratic (x, xstar) = P.toDual xstar x)

/- Infrastructure D.1 (Quadratic pairing on a Banach-dual product) (2) -/
#check (DualPairing.symmetric :
  DualPairing X Xstar → LinearMap.BilinForm ℝ (X × Xstar))
#check (DualPairing.symmetric_apply :
  ∀ (P : DualPairing X Xstar) (x y : X) (xstar ystar : Xstar),
    P.symmetric (x, xstar) (y, ystar) = P.toDual ystar x + P.toDual xstar y)
