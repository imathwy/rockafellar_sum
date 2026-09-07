module

public import ReasLib.MeasureTheory.UnitL2.Primitive

@[expose] public section

open MeasureTheory

namespace UnitL2

/- Infrastructure B.9 (A zero indefinite integral determines an L² function):
If every initial interval integral of `y : UnitL2` vanishes, then `y` is zero. -/
#check (UnitL2.eq_zero_of_primitive_eq_zero :
  ∀ (y : UnitL2),
    (∀ t ∈ Set.Icc (0 : ℝ) 1, (∫ s in (0 : ℝ)..t, y s) = 0) → y = 0)

end UnitL2
