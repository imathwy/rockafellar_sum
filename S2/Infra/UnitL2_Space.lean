/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2

/-!
# The real `UnitL2` space

This source-facing module records the unit-interval `L2` type and its canonical
almost-everywhere representative API.
-/

#check (UnitL2 : Type)
#check (UnitL2.toAEEqFun :
  UnitL2 →ₗ[ℝ] (ℝ →ₘ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)] ℝ))
#check (UnitL2.toAEEqFun_apply :
  ∀ (f : UnitL2) (x : ℝ), UnitL2.toAEEqFun f x = f x)
#check (UnitL2.ext_iff :
  ∀ (f g : UnitL2), f = g ↔ UnitL2.toAEEqFun f = UnitL2.toAEEqFun g)
