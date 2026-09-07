module

public import ReasLib.MeasureTheory.UnitL2

#check (UnitL2 : Type)
#check (UnitL2.toAEEqFun :
  UnitL2 →ₗ[ℝ] (ℝ →ₘ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)] ℝ))
#check (UnitL2.toAEEqFun_apply :
  ∀ (f : UnitL2) (x : ℝ), UnitL2.toAEEqFun f x = f x)
#check (UnitL2.ext_iff :
  ∀ (f g : UnitL2), f = g ↔ UnitL2.toAEEqFun f = UnitL2.toAEEqFun g)
