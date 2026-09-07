/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Integrability of `UnitL2` representatives

This module records integrability and norm bounds for canonical unit-interval
`L2` representatives.
-/

@[expose] public section

open MeasureTheory

namespace UnitL2

/-- The canonical function representative of a real `UnitL2` vector is integrable on the
unit interval. -/
theorem integrable_coeFn (f : UnitL2) :
    Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  -- Finite measure lets the canonical `L²` representative descend to `L¹`.
  exact (Lp.memLp f).integrable fact_one_le_two_ennreal.elim

/-- The integral of the pointwise norm of a real `UnitL2` vector over the unit interval is
bounded by its `L²` norm. -/
theorem integral_norm_le_norm (f : UnitL2) :
    (∫ x, ‖f x‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤ ‖f‖ := by
  have hf : AEStronglyMeasurable (f : ℝ → ℝ)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := Lp.aestronglyMeasurable f
  -- Express the integral and the bundled norm using the same extended `Lᵖ` seminorm.
  rw [← lpNorm_one_eq_integral_norm hf, ← toReal_eLpNorm hf, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  -- Hölder's finite-measure comparison has unit factor on `(0, 1]`.
  simpa [Measure.restrict_apply_univ, Real.volume_Ioc] using
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ fact_one_le_two_ennreal.elim hf)

end UnitL2
