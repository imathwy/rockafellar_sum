module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint

public section

noncomputable section

open scoped InnerProductSpace

/- Compatibility bridge for the interval-coordinate adjoint data. -/
#check (L1Seq.intervalCoordinateAdjoint : UnitL2 →L[ℝ] StrongDual ℝ L1Seq)

/- Compatibility bridge for evaluation of the interval-coordinate adjoint. -/
#check (L1Seq.intervalCoordinateAdjoint_apply :
  ∀ (y : UnitL2) (a : L1Seq),
    L1Seq.intervalCoordinateAdjoint y a =
      ⟪y, L1Seq.intervalCoordinateOperator a⟫_ℝ)
