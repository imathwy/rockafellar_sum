/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex

/-!
# Folded right-vertex coordinates

This module records the positive and negative coordinate formulas for folded
detector perturbations and vertices.
-/

public section

namespace Lorentz

/-- Every folded detector perturbation has zero positive coordinate. -/
theorem positiveCoordinate_detectorPerturbation (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    positiveCoordinate d hd
      (detectorPerturbation d hd h_missing h h_tendsto i) = 0 := by
  -- Expose the perturbation as a scaled scheduled detector and use linearity.
  rw [detectorPerturbation_apply, map_smul, scheduledDetectorPoint_apply]
  rw [h_positive]
  simp only [smul_zero]

/-- The positive coordinate of every folded right vertex is its scheduled right time. -/
theorem positiveCoordinate_rightVertex (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    positiveCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) =
      DetectorTriple.rightTime i := by
  -- Split the vertex into its near-ghost base and detector perturbation.
  rw [rightVertex_apply, map_add]
  -- The base supplies the scheduled time, while the perturbation contributes zero.
  rw [positiveCoordinate_nearGhostBase]
  rw [positiveCoordinate_detectorPerturbation d hd h_missing h h_positive h_tendsto i]
  simp only [add_zero]

/-- The negative-coordinate norm of every folded right vertex is strictly less
than its scheduled right radius. -/
theorem norm_negativeCoordinate_rightVertex_lt (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i)‖ <
      DetectorTriple.rightRadius i := by
  -- Start from the two established half-radius estimates.
  have hbase := norm_negativeCoordinate_nearGhostBase_lt d hd h_missing i
  have hpert := scaled_norm_detectorIndex_lt d hd h_missing h h_tendsto i
  have hpert' : ‖negativeCoordinate d hd
      (detectorPerturbation d hd h_missing h h_tendsto i)‖ <
      DetectorTriple.rightRadius i / 2 := by
    -- Normalize the perturbation norm; either scheduled sign has norm one.
    rw [detectorPerturbation_apply, map_smul, norm_smul]
    rcases DetectorTriple.coe_sign_eq_neg_one_or_one
      (DetectorTriple.schedule.toFun i) with hsign | hsign
    · rw [hsign]
      simpa only [norm_mul, norm_neg, norm_one, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (detectorScale_pos d hd h_missing i).le] using hpert
    · rw [hsign]
      simpa only [norm_mul, norm_one, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (detectorScale_pos d hd h_missing i).le] using hpert
  rw [rightVertex_apply, map_add]
  calc
    ‖negativeCoordinate d hd (nearGhostBase d hd h_missing i) +
        negativeCoordinate d hd (detectorPerturbation d hd h_missing h h_tendsto i)‖ ≤
        ‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖ +
          ‖negativeCoordinate d hd (detectorPerturbation d hd h_missing h h_tendsto i)‖ :=
      norm_add_le _ _
    _ < DetectorTriple.rightRadius i := by
      -- Add the strict bounds and identify the sum of the two half-radii.
      have hsumlt := add_lt_add hbase hpert'
      have hhalves : DetectorTriple.rightRadius i / 2 +
          DetectorTriple.rightRadius i / 2 = DetectorTriple.rightRadius i := by
        ring
      rw [hhalves] at hsumlt
      exact hsumlt

end Lorentz
