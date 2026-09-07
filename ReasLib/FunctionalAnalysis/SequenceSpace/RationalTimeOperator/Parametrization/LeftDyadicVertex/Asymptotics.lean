/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex

/-!
# Left-Dyadic Asymptotics

This module proves convergence and norm bounds for the selected left dyadic vertices.
-/

public section

open Filter Topology

namespace Lorentz

/-- The left dyadic radius is one sixteenth of the gap from its time to `1`. -/
private lemma leftRadius_eq_one_div_16_mul_gap (k : ℕ) :
    leftRadius k = (1 / 16 : ℝ) * (1 - leftTime k) := by
  -- Split the radius exponent into the time-gap exponent and the fixed factor `2⁻⁴`.
  rw [leftRadius_def, leftTime_def]
  have htwo : (0 : ℝ) < 2 := by
    norm_num
  have hexponent : (-(k + 5 : ℝ)) = (-4 : ℝ) + (-(k + 1 : ℝ)) := by
    ring
  rw [hexponent, Real.rpow_add htwo]
  norm_num

/-- A selected left vertex has negative-coordinate norm below three thirty-seconds
of its remaining time gap. -/
private lemma norm_negativeCoordinate_leftVertex_lt_three_div_32_mul_gap
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ) :
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ <
      (3 / 32 : ℝ) * (1 - leftTime k) := by
  -- The remaining dyadic time gap is positive.
  have hgap : 0 < 1 - leftTime k := by
    rw [leftTime_def]
    have hbase : (0 : ℝ) < 2 := by
      norm_num
    have hp : 0 < (2 : ℝ) ^ (-(k + 1 : ℝ)) :=
      Real.rpow_pos_of_pos hbase _
    linarith
  -- Scale the initial norm bound to control the affine template.
  have htemplate :
      ‖leftTemplate (negativeCoordinate d hd z₀) (leftTime k)‖ <
        (1 / 32 : ℝ) * (1 - leftTime k) := by
    rw [leftTemplate_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hgap]
    nlinarith
  -- Add the prescribed approximation error to the template estimate.
  have hvertex := norm_negativeCoordinate_leftVertex_sub_leftTemplate_lt
    d hd h_missing z₀ k
  rw [leftRadius_eq_one_div_16_mul_gap] at hvertex
  calc
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ =
        ‖(negativeCoordinate d hd (leftVertex d hd h_missing z₀ k) -
            leftTemplate (negativeCoordinate d hd z₀) (leftTime k)) +
          leftTemplate (negativeCoordinate d hd z₀) (leftTime k)‖ := by
            rw [sub_add_cancel]
    _ ≤ ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ k) -
          leftTemplate (negativeCoordinate d hd z₀) (leftTime k)‖ +
        ‖leftTemplate (negativeCoordinate d hd z₀) (leftTime k)‖ :=
      norm_add_le _ _
    _ < (1 / 16 : ℝ) * (1 - leftTime k) +
        (1 / 32 : ℝ) * (1 - leftTime k) := add_lt_add hvertex htemplate
    _ = (3 / 32 : ℝ) * (1 - leftTime k) := by ring

/-- The negative coordinates of the selected left dyadic vertices converge to zero. -/
theorem leftVertex_tendsto_ghost (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) :
    Tendsto (fun k ↦ negativeCoordinate d hd (leftVertex d hd h_missing z₀ k))
      atTop (𝓝 0) := by
  -- The remaining-time gap vanishes because the dyadic times converge to `1`.
  have hgap : Tendsto (fun k : ℕ ↦ 1 - leftTime k) atTop (𝓝 0) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_leftTime using 1
    norm_num
  have henvelope :
      Tendsto (fun k : ℕ ↦ (3 / 32 : ℝ) * (1 - leftTime k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hgap
  -- Squeeze the chosen vertices by the common scalar envelope.
  refine squeeze_zero_norm
    (f := fun k ↦ negativeCoordinate d hd (leftVertex d hd h_missing z₀ k))
    (a := fun k ↦ (3 / 32 : ℝ) * (1 - leftTime k)) (fun k ↦ ?_) henvelope
  exact (norm_negativeCoordinate_leftVertex_lt_three_div_32_mul_gap
    d hd h_missing z₀ hN₀ k).le

/-- Every selected left dyadic vertex satisfies the strict norm bound between its time
and the ghost time `1`. -/
theorem leftVertex_norm_lt (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) :
    ∀ k, ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ <
      1 - leftTime k := by
  intro k
  -- The common envelope is strictly smaller than the positive remaining-time gap.
  have henvelope := norm_negativeCoordinate_leftVertex_lt_three_div_32_mul_gap
    d hd h_missing z₀ hN₀ k
  have hgap : 0 < 1 - leftTime k := by
    rw [leftTime_def]
    have hbase : (0 : ℝ) < 2 := by
      norm_num
    have hp : 0 < (2 : ℝ) ^ (-(k + 1 : ℝ)) :=
      Real.rpow_pos_of_pos hbase _
    linarith
  nlinarith

end Lorentz
