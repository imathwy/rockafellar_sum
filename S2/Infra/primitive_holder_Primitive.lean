/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.Primitive

/-!
# Primitive functions for `UnitL2`

This compatibility module exposes the primitive function and its interval-integral
evaluation formula.
-/

@[expose] public section

open MeasureTheory

/- The shared primitive API remains available through this compatibility module. -/
#check (UnitL2.primitive : UnitL2 → ℝ → ℝ)

/- Its evaluation theorem records the defining interval integral. -/
#check (UnitL2.primitive_apply :
  ∀ (y : UnitL2) (t : ℝ), UnitL2.primitive y t = ∫ s in (0 : ℝ)..t, y s)
