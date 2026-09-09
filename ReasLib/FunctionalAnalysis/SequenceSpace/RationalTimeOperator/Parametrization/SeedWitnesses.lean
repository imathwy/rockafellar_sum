/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedAssembly

/-!
# Concrete source witnesses for the S3 seed
-/

public section

namespace Lorentz

/-- The source direction is an explicit remote unit-difference base with
positive time one, small negative coordinate and bounded primal component. -/
theorem exists_seed_direction : ∃ v : parametrizedSubspace axisDirection,
    positiveCoordinate axisDirection seed_axis_ne_zero v = 1 ∧
    ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ < 1 / 64 ∧
    ‖(v : C0Seq × L1Seq).1‖ ≤ 5 := by
  have hε : (0 : ℝ) < 1 / 64 := by norm_num
  obtain ⟨r, hr, hsmall⟩ := exists_remote_unitDifference_norm_lt 1 2 (1 / 64) hε
  have hrone : r ≠ 1 := by omega
  refine ⟨axisSeedBase ((1 : ℝ) • unitDifference 1 r) 1, ?_, ?_, ?_⟩
  · exact positiveCoordinate_axisSeedBase _ _ _
  · rw [norm_negativeCoordinate_axisSeedBase r hrone,
      abs_one, one_mul, ← norm_intervalCoordinate_unitDifference]
    exact hsmall
  · simpa only [abs_one, mul_one] using norm_axisSeedBase_fst_le r hrone 1

/-- Twice a source direction lies strictly inside the radius-twelve primal ball. -/
theorem seed_anchor_primal_lt_twelve (v : parametrizedSubspace axisDirection)
    (hv : ‖(v : C0Seq × L1Seq).1‖ ≤ 5) :
    ‖(((2 : ℝ) • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq).1‖ < 12 := by
  simp only [Submodule.coe_smul, Prod.smul_fst, norm_smul, Real.norm_eq_abs]
  norm_num
  linarith

end Lorentz
