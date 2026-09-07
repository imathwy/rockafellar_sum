/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint
public import ReasLib.MeasureTheory.UnitL2.RationalIntervalIndicator.Integral

/-!
# Adjoint formula for `V`

This source-facing module records the two canonical evaluations of the
interval-coordinate adjoint.
-/

public section

noncomputable section

open scoped InnerProductSpace

/- Lemma 2.8 (Adjoint formula for $V$) (1): the `n`th standard-coordinate
evaluation of `intervalCoordinateAdjoint y` is its inner product with the `n`th
interval-indicator vector. -/
#check (L1Seq.intervalCoordinateAdjoint_apply_single :
  ∀ (y : UnitL2) (n : ℕ),
    L1Seq.intervalCoordinateAdjoint y (lp.single 1 n (1 : ℝ)) =
      ⟪y, UnitL2.rationalIntervalVec n⟫_ℝ)

/- Lemma 2.8 (Adjoint formula for $V$) (2): the inner product with the `n`th
interval-indicator vector is the interval integral through `rationalTime n`. -/
#check (UnitL2.inner_rationalIntervalVec_eq_integral :
  ∀ (y : UnitL2) (n : ℕ),
    ⟪y, UnitL2.rationalIntervalVec n⟫_ℝ =
      ∫ s in (0 : ℝ)..rationalTime n, y s)
