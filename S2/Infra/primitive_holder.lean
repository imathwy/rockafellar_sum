/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.Primitive.Holder

/-!
# Holder estimates for `UnitL2` primitives

This module exposes square-root Holder continuity and ordinary continuity of
primitive functions on the unit interval.
-/

@[expose] public section

/- Infrastructure B.8 (Hölder continuity of the indefinite integral) (1).
For a real `UnitL2` vector `y`, its primitive satisfies the square-root Hölder estimate
on `Set.Icc 0 1`. -/
#check (UnitL2.abs_primitive_sub_le :
  ∀ (y : UnitL2) {r t : ℝ}, r ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
    |UnitL2.primitive y t - UnitL2.primitive y r| ≤ ‖y‖ * Real.sqrt |t - r|)

/- The primitive of a real `UnitL2` vector is Hölder continuous with exponent `1 / 2`
and constant `‖y‖₊` on the unit interval. -/
#check (UnitL2.holderOnWith_primitive :
  ∀ y : UnitL2,
    HolderOnWith ‖y‖₊ (1 / 2 : NNReal) (UnitL2.primitive y) (Set.Icc (0 : ℝ) 1))

/- Infrastructure B.8 (Hölder continuity of the indefinite integral) (2).
The primitive of a real `UnitL2` vector is continuous on `Set.Icc 0 1`. -/
#check (UnitL2.continuousOn_primitive :
  ∀ y : UnitL2, ContinuousOn (UnitL2.primitive y) (Set.Icc (0 : ℝ) 1))
