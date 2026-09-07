/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ReasLib.MeasureTheory.UnitL2.RationalIntervalIndicator

/-!
# Rational interval-indicator integrals

This module identifies inner products with rational interval-indicator
vectors with the corresponding interval integrals.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace UnitL2

/-- The inner product with the `n`th rational interval-indicator vector equals the
interval integral through the corresponding rational time. -/
theorem inner_rationalIntervalVec_eq_integral (y : UnitL2) (n : ℕ) :
    ⟪y, rationalIntervalVec n⟫_ℝ =
      ∫ s in (0 : ℝ)..rationalTime n, y s := by
  have hsubset :
      Set.Ioo (0 : ℝ) (rationalTime n) ⊆ Set.Ioc (0 : ℝ) 1 := by
    -- The rational endpoint lies strictly inside the ambient unit interval.
    intro s hs
    exact ⟨hs.1, hs.2.le.trans (rationalTime_mem_Ioo n).2.le⟩
  -- Commute the inner product so the canonical indicator formula applies on the left.
  rw [real_inner_comm]
  unfold rationalIntervalVec intervalVec
  -- Collapse the nested restriction, then identify the set integral with the interval integral.
  rw [MeasureTheory.L2.inner_indicatorConstLp_one,
    MeasureTheory.Measure.restrict_restrict_of_subset hsubset,
    intervalIntegral.integral_of_le (rationalTime_mem_Ioo n).1.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

end UnitL2
