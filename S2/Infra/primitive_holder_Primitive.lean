module

public import ReasLib.MeasureTheory.UnitL2.Primitive

@[expose] public section

open MeasureTheory

/- The shared primitive API remains available through this compatibility module. -/
#check (UnitL2.primitive : UnitL2 → ℝ → ℝ)

/- Its evaluation theorem records the defining interval integral. -/
#check (UnitL2.primitive_apply :
  ∀ (y : UnitL2) (t : ℝ), UnitL2.primitive y t = ∫ s in (0 : ℝ)..t, y s)
