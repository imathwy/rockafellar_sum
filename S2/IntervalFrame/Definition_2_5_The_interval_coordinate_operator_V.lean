module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator

/- Definition 2.5 (The interval-coordinate operator $V$) (1):
the operator and its series formula. -/
#check (L1Seq.intervalCoordinateOperator : L1Seq →L[ℝ] UnitL2)
#check (L1Seq.intervalCoordinateOperator_apply :
  ∀ a : L1Seq,
    L1Seq.intervalCoordinateOperator a =
      ∑' n : ℕ, a n • UnitL2.rationalIntervalVec n)

/- Definition 2.5 (The interval-coordinate operator $V$) (2):
absolute convergence of the defining series. -/
#check (L1Seq.summable_norm_smul_rationalIntervalVec :
  ∀ a : L1Seq,
    Summable (fun n : ℕ ↦ ‖a n • UnitL2.rationalIntervalVec n‖))

/- Definition 2.5 (The interval-coordinate operator $V$) (3):
the pointwise and operator-norm estimates. -/
#check (L1Seq.norm_intervalCoordinateOperator_apply_le :
  ∀ a : L1Seq, ‖L1Seq.intervalCoordinateOperator a‖ ≤ ‖a‖)
#check (L1Seq.norm_intervalCoordinateOperator_le :
  ‖L1Seq.intervalCoordinateOperator‖ ≤ 1)
