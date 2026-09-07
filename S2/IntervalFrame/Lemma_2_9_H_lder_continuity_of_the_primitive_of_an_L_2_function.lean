/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.Primitive.Holder
public import ReasLib.MeasureTheory.UnitL2.Primitive.AbsolutelyContinuous

/-!
# Primitive Regularity

This module exposes integral, Holder, continuity, and absolute-continuity facts for primitives.
-/

@[expose] public section

open MeasureTheory

/- Lemma 2.9 (Hölder continuity of the primitive of an $L^2$ function) (1).
The primitive is given by its defining interval integral. -/
#check (UnitL2.primitive_apply :
  ∀ (y : UnitL2) (t : ℝ), UnitL2.primitive y t = ∫ s in (0 : ℝ)..t, y s)

/- Lemma 2.9 (Hölder continuity of the primitive of an $L^2$ function) (2).
The primitive satisfies the square-root Hölder estimate on `Set.Icc 0 1`. -/
#check (UnitL2.abs_primitive_sub_le :
  ∀ (y : UnitL2) {r t : ℝ}, r ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
    |UnitL2.primitive y t - UnitL2.primitive y r| ≤ ‖y‖ * Real.sqrt |t - r|)

/- Lemma 2.9 (Hölder continuity of the primitive of an $L^2$ function) (3).
The primitive is continuous on `Set.Icc 0 1`. -/
#check (UnitL2.continuousOn_primitive :
  ∀ y : UnitL2, ContinuousOn (UnitL2.primitive y) (Set.Icc (0 : ℝ) 1))

/- Lemma 2.9 (Hölder continuity of the primitive of an $L^2$ function) (4).
The primitive is absolutely continuous on the unit interval. -/
#check (UnitL2.absolutelyContinuousOnInterval_primitive :
  ∀ y : UnitL2, AbsolutelyContinuousOnInterval (UnitL2.primitive y) 0 1)

/- Lemma 2.9 (Hölder continuity of the primitive of an $L^2$ function) (5).
The derivative of the primitive is `y` almost everywhere on the represented unit interval. -/
#check (UnitL2.ae_hasDerivAt_primitive :
  ∀ y : UnitL2, ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
    HasDerivAt (UnitL2.primitive y) (y t) t)
