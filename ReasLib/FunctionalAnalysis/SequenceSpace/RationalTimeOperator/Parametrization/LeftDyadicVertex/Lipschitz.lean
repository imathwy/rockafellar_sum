/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex

/-!
# Lipschitz bounds for left dyadic vertices

This module proves the local slope estimates for consecutive left dyadic
vertices and their affine edges.
-/

public section

namespace Lorentz

/-- Consecutive left dyadic radii sum to three sixteenths of the corresponding time gap. -/
private lemma leftRadius_succ_add (k : ℕ) :
    leftRadius (k + 1) + leftRadius k =
      (3 / 16 : ℝ) * (leftTime (k + 1) - leftTime k) := by
  -- Express both radii as fixed dyadic multiples of the common time gap.
  rw [leftRadius_def, leftRadius_def, leftTime_succ_sub]
  have htwo : (0 : ℝ) < 2 := by
    norm_num
  have hsucc : (-(↑(k + 1) + 5 : ℝ)) = -(k + 2 : ℝ) + (-4 : ℝ) := by
    push_cast
    ring
  have hcurrent : (-(k + 5 : ℝ)) = -(k + 2 : ℝ) + (-3 : ℝ) := by
    ring
  rw [hsucc, hcurrent, Real.rpow_add htwo, Real.rpow_add htwo]
  norm_num
  ring

/-- The negative coordinates of consecutive left vertices satisfy the combined
endpoint-error and template-increment bound. -/
private lemma dist_negativeCoordinate_leftVertex_succ_lt_budget
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ) :
    dist (negativeCoordinate d hd (leftVertex d hd h_missing z₀ (k + 1)))
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)) <
      leftRadius (k + 1) +
        (1 / 32 : ℝ) * (leftTime (k + 1) - leftTime k) + leftRadius k := by
  -- Take the two strict endpoint estimates from the selected-vertex specification.
  have hnext := norm_negativeCoordinate_leftVertex_sub_leftTemplate_lt
    d hd h_missing z₀ (k + 1)
  have hcurrent := norm_negativeCoordinate_leftVertex_sub_leftTemplate_lt
    d hd h_missing z₀ k
  have hcurrentReversed :
      ‖leftTemplate (negativeCoordinate d hd z₀) (leftTime k) -
          negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ < leftRadius k := by
    rw [norm_sub_rev]
    exact hcurrent
  -- Convert the template Lipschitz estimate to the positive adjacent time gap.
  have hgap : 0 < leftTime (k + 1) - leftTime k := by
    rw [leftTime_succ_sub]
    positivity
  have htimeDist :
      dist (leftTime (k + 1)) (leftTime k) = leftTime (k + 1) - leftTime k := by
    rw [Real.dist_eq, abs_of_pos hgap]
  have htemplate :=
    (lipschitzWith_leftTemplate_one_div_32
      (negativeCoordinate d hd z₀) hN₀).dist_le_mul
      (leftTime (k + 1)) (leftTime k)
  rw [htimeDist] at htemplate
  norm_num [NNReal.coe_div] at htemplate
  simp only [dist_eq_norm] at htemplate
  -- The four-point triangle inequality combines the three controlled pieces.
  have htriangle := dist_triangle4
    (negativeCoordinate d hd (leftVertex d hd h_missing z₀ (k + 1)))
    (leftTemplate (negativeCoordinate d hd z₀) (leftTime (k + 1)))
    (leftTemplate (negativeCoordinate d hd z₀) (leftTime k))
    (negativeCoordinate d hd (leftVertex d hd h_missing z₀ k))
  simp only [dist_eq_norm] at htriangle
  rw [dist_eq_norm]
  linarith

/-- Consecutive selected left dyadic vertices have negative-coordinate displacement
strictly smaller than their dyadic time gap. -/
theorem leftVertex_slope_lt_one (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ) :
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ (k + 1)) -
        negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ <
      leftTime (k + 1) - leftTime k := by
  -- First package the displacement as the sum of the two endpoint errors and template motion.
  have hbudget := dist_negativeCoordinate_leftVertex_succ_lt_budget
    d hd h_missing z₀ hN₀ k
  simp only [dist_eq_norm] at hbudget
  -- Normalize both radii against the same positive gap and compare coefficients.
  have hradii := leftRadius_succ_add k
  have hgap : 0 < leftTime (k + 1) - leftTime k := by
    rw [leftTime_succ_sub]
    positivity
  nlinarith

/-- The negative-coordinate displacement from a time-zero point to the first selected
left dyadic vertex is strictly smaller than the first dyadic time. -/
theorem initialLeftVertex_slope_lt_one (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd z₀ = 0)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) :
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
        negativeCoordinate d hd z₀‖ < leftTime 0 := by
  have hvertex := norm_negativeCoordinate_leftVertex_sub_leftTemplate_lt
    d hd h_missing z₀ 0
  have htime : leftTime 0 = (1 / 2 : ℝ) := by
    rw [leftTime_def]
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hrad : leftRadius 0 = (1 / 32 : ℝ) := by
    rw [leftRadius_def]
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have htemplate :
      ‖leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
          negativeCoordinate d hd z₀‖ < (1 / 64 : ℝ) := by
    rw [htime, leftTemplate_apply]
    have hdiff : (1 - (1 / 2 : ℝ)) • negativeCoordinate d hd z₀ -
        negativeCoordinate d hd z₀ = -(1 / 2 : ℝ) • negativeCoordinate d hd z₀ := by
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)]
    nlinarith
  have hvertex' :
      ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
          leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)‖ <
        (1 / 32 : ℝ) := by
    exact lt_of_lt_of_eq hvertex hrad
  have hdecomp :
      negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
          negativeCoordinate d hd z₀ =
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
            leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)) +
          (leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
            negativeCoordinate d hd z₀) := by
    module
  calc
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
        negativeCoordinate d hd z₀‖ =
        ‖(negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
            leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)) +
          (leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
            negativeCoordinate d hd z₀)‖ := congrArg norm hdecomp
    _ ≤ ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
          leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)‖ +
        ‖leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
          negativeCoordinate d hd z₀‖ := norm_add_le _ _
    _ < leftTime 0 := by nlinarith [hvertex', htemplate, htime]

end Lorentz
