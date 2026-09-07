module

public import ReasLib.MeasureTheory.UnitL2.IntervalIndicator

public section

open scoped InnerProductSpace

/- Infrastructure B.3 (Gram identity for interval indicators) (1).
The inner product of two interval-indicator vectors is the minimum of their endpoints. -/
#check (UnitL2.inner_intervalVec :
  ∀ s t : unitInterval,
    ⟪UnitL2.intervalVec s, UnitL2.intervalVec t⟫_ℝ = min (s : ℝ) (t : ℝ))

/- Infrastructure B.3 (Gram identity for interval indicators) (2).
The squared norm of an interval-indicator vector is its endpoint. -/
#check (UnitL2.norm_sq_intervalVec :
  ∀ t : unitInterval, ‖UnitL2.intervalVec t‖ ^ 2 = (t : ℝ))
