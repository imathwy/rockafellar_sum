/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.ProductPairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Folded right-vertex bounds

This module records quadratic, norm, and cone bounds for folded detector
perturbations.
-/

public section

open scoped InnerProductSpace

namespace Lorentz

/-- The quadratic pairing of a folded detector perturbation is the negative square
of the norm of its negative Lorentz coordinate. -/
theorem quadraticPairing_detectorPerturbation_eq_neg_sq
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    C0Seq.quadraticPairing
      (detectorPerturbation d hd h_missing h h_tendsto i) =
        -‖negativeCoordinate d hd
          (detectorPerturbation d hd h_missing h h_tendsto i)‖ ^ 2 := by
  rw [quadraticIdentity d hd]
  rw [positiveCoordinate_detectorPerturbation d hd h_missing h h_positive h_tendsto i]
  simp

/-- Every folded detector perturbation has nonpositive quadratic pairing. -/
theorem quadraticPairing_detectorPerturbation_nonpos (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    C0Seq.quadraticPairing
      (detectorPerturbation d hd h_missing h h_tendsto i) ≤ 0 := by
  -- The exact coordinate identity exposes the pairing as a negative square.
  rw [quadraticPairing_detectorPerturbation_eq_neg_sq d hd h_missing h h_positive h_tendsto i]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- The absolute pairing of a near-ghost base point with its detector perturbation
is strictly bounded by half the square of the scheduled radius. -/
theorem abs_symmetricForm_nearGhostBase_detectorPerturbation_lt
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    |C0Seq.symmetricForm (nearGhostBase d hd h_missing i)
      (detectorPerturbation d hd h_missing h h_tendsto i)| <
        DetectorTriple.rightRadius i ^ 2 / 2 := by
  -- Vanishing of the perturbation's positive coordinate reduces the form to one inner product.
  have hform : C0Seq.symmetricForm (nearGhostBase d hd h_missing i)
      (detectorPerturbation d hd h_missing h h_tendsto i) =
      -2 * ⟪negativeCoordinate d hd (nearGhostBase d hd h_missing i),
        negativeCoordinate d hd
          (detectorPerturbation d hd h_missing h h_tendsto i)⟫_ℝ := by
    rw [symmetricForm_eq_coordinates d hd]
    rw [positiveCoordinate_detectorPerturbation d hd h_missing h h_positive h_tendsto i]
    ring
  rw [hform]
  -- Normalize the signed detector scale so both coordinate norms use the same radius bound.
  have hNξ := norm_negativeCoordinate_nearGhostBase_lt d hd h_missing i
  have hNδ := scaled_norm_detectorIndex_lt d hd h_missing h h_tendsto i
  have hNδ' : ‖negativeCoordinate d hd
      (detectorPerturbation d hd h_missing h h_tendsto i)‖ <
      DetectorTriple.rightRadius i / 2 := by
    rw [detectorPerturbation_apply, map_smul, norm_smul]
    have hsign_norm : ‖((DetectorTriple.schedule.toFun i).sign : ℝ)‖ = (1 : ℝ) := by
      rcases DetectorTriple.coe_sign_eq_neg_one_or_one
        (DetectorTriple.schedule.toFun i) with hsign | hsign
      · simp only [hsign, Real.norm_eq_abs, abs_neg, abs_one]
      · simp only [hsign, Real.norm_eq_abs, abs_one]
    rw [norm_mul, hsign_norm]
    have hscale_norm : ‖detectorScale d hd h_missing i‖ =
        detectorScale d hd h_missing i := by
      rw [Real.norm_eq_abs, abs_of_pos (detectorScale_pos d hd h_missing i)]
    rw [hscale_norm, one_mul]
    exact hNδ
  -- Cauchy–Schwarz and the two strict half-radius estimates give the desired product bound.
  have habsinner := abs_real_inner_le_norm
    (negativeCoordinate d hd (nearGhostBase d hd h_missing i))
    (negativeCoordinate d hd
      (detectorPerturbation d hd h_missing h h_tendsto i))
  have hprod : ‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖ *
      ‖negativeCoordinate d hd (detectorPerturbation d hd h_missing h h_tendsto i)‖ <
      (DetectorTriple.rightRadius i / 2) ^ 2 := by
    simpa only [pow_two] using
      (mul_lt_mul_of_nonneg hNξ hNδ' (norm_nonneg _) (norm_nonneg _))
  calc
    |-2 * ⟪negativeCoordinate d hd (nearGhostBase d hd h_missing i),
        negativeCoordinate d hd
          (detectorPerturbation d hd h_missing h h_tendsto i)⟫_ℝ| =
        2 * |⟪negativeCoordinate d hd (nearGhostBase d hd h_missing i),
        negativeCoordinate d hd
          (detectorPerturbation d hd h_missing h h_tendsto i)⟫_ℝ| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * (‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖ *
        ‖negativeCoordinate d hd
          (detectorPerturbation d hd h_missing h h_tendsto i)‖) := by
      gcongr
    _ < DetectorTriple.rightRadius i ^ 2 / 2 := by
      nlinarith [hprod]

/-- The absolute quadratic pairing of each near-ghost base point is at most `9 / 4`. -/
theorem abs_quadraticPairing_nearGhostBase_le (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
    |C0Seq.quadraticPairing (nearGhostBase d hd h_missing i)| ≤ (9 : ℝ) / 4 := by
  -- Expand the Lorentz energy and bound its scheduled positive coordinate.
  have hq := quadraticIdentity d hd (nearGhostBase d hd h_missing i)
  rw [positiveCoordinate_nearGhostBase d hd h_missing i] at hq
  have hP_nonneg : 0 ≤ DetectorTriple.rightTime i := by
    rw [DetectorTriple.rightTime_def]
    positivity
  have hP_le : DetectorTriple.rightTime i ≤ (3 : ℝ) / 2 := by
    rw [DetectorTriple.rightTime_def]
    have hi : (0 : ℝ) ≤ i := by positivity
    have hexp : -(i + 1 : ℝ) ≤ (-1 : ℝ) := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hpow' : (2 : ℝ) ^ (-(i + 1 : ℝ)) ≤ (1 : ℝ) / 2 := by
      convert hpow using 1
      ring
    linarith
  -- The radius estimate turns the near-ghost negative-coordinate bound into a uniform half bound.
  have hr : DetectorTriple.rightRadius i ≤ (1 : ℝ) := by
    rw [DetectorTriple.rightRadius_def]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hi : (0 : ℝ) ≤ i := by positivity
    linarith
  have hN_nonneg := norm_nonneg
    (negativeCoordinate d hd (nearGhostBase d hd h_missing i))
  have hN_lt := norm_negativeCoordinate_nearGhostBase_lt d hd h_missing i
  have hN_le : ‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖ ≤
      (1 : ℝ) / 2 := by
    have : DetectorTriple.rightRadius i / 2 ≤ (1 : ℝ) / 2 := by nlinarith
    exact hN_lt.le.trans this
  have hPsq : DetectorTriple.rightTime i ^ 2 ≤ ((3 : ℝ) / 2) ^ 2 := by
    simpa only [pow_two] using
      (mul_self_le_mul_self hP_nonneg hP_le)
  have hNsq : ‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖ ^ 2 ≤
      ((1 : ℝ) / 2) ^ 2 := by
    simpa only [pow_two] using
      (mul_self_le_mul_self hN_nonneg hN_le)
  -- The two square estimates control both sides of the final absolute-value inequality.
  have hq_upper : C0Seq.quadraticPairing (nearGhostBase d hd h_missing i) ≤
      (9 : ℝ) / 4 := by
    nlinarith [hq, hPsq, sq_nonneg
      (‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖)]
  apply (abs_le).2
  constructor
  · nlinarith [hq, hNsq, sq_nonneg (DetectorTriple.rightTime i)]
  · exact hq_upper

/-- Pairing any ambient point with a near-ghost base point is bounded by the product
of their coordinate-sum sizes. -/
theorem abs_symmetricForm_nearGhostBase_le_zSize (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (w : C0Seq × L1Seq) (i : ℕ) :
    |C0Seq.symmetricForm w (nearGhostBase d hd h_missing i)| ≤
      C0Seq.zSize w * C0Seq.zSize (nearGhostBase d hd h_missing i) := by
  -- Expand the symmetric form into its two coordinate pairings.
  rw [C0Seq.symmetricForm_apply]
  change |C0Seq.pairingL w.1 (nearGhostBase d hd h_missing i).1.2 +
      C0Seq.pairingL (nearGhostBase d hd h_missing i).1.1 w.2| ≤
    C0Seq.zSize w * C0Seq.zSize (nearGhostBase d hd h_missing i)
  rw [C0Seq.zSize_apply]
  -- Bound each pairing by the corresponding norm product and collect the four terms.
  calc
    |C0Seq.pairingL w.1 (nearGhostBase d hd h_missing i).1.2 +
        C0Seq.pairingL (nearGhostBase d hd h_missing i).1.1 w.2| ≤
        |C0Seq.pairingL w.1 (nearGhostBase d hd h_missing i).1.2| +
          |C0Seq.pairingL (nearGhostBase d hd h_missing i).1.1 w.2| :=
      abs_add_le _ _
    _ ≤ ‖w.1‖ * ‖(nearGhostBase d hd h_missing i).1.2‖ +
        ‖(nearGhostBase d hd h_missing i).1.1‖ * ‖w.2‖ := by
      gcongr
      · simpa only [C0Seq.pairingL_apply] using
          C0Seq.abs_tsum_mul_le w.1 (nearGhostBase d hd h_missing i).1.2
      · simpa only [C0Seq.pairingL_apply] using
          C0Seq.abs_tsum_mul_le (nearGhostBase d hd h_missing i).1.1 w.2
    _ ≤ (‖w.1‖ + ‖w.2‖) *
        C0Seq.zSize (nearGhostBase d hd h_missing i) := by
      rw [C0Seq.zSize_apply]
      nlinarith [norm_nonneg w.1, norm_nonneg w.2,
        norm_nonneg (nearGhostBase d hd h_missing i).1.1,
        norm_nonneg (nearGhostBase d hd h_missing i).1.2]

end Lorentz
