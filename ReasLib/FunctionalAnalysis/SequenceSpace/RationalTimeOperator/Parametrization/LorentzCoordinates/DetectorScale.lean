/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.NearGhostBase
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.ProductPairing

/-!
# Detector scales

This module defines the quadratic detector scale attached to near-ghost base
points and its elementary bounds.
-/

public section

namespace Lorentz

/-- The scale attached to the `i`-th near-ghost base point is its quadratic
index weight times one plus its coordinate-sum size. -/
noncomputable def detectorScale (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) : ℕ → ℝ :=
  fun i ↦ ((i + 1 : ℕ) : ℝ) ^ 2 *
    (1 + C0Seq.zSize (nearGhostBase d hd h_missing i))

/-- The detector scale evaluates to its prescribed quadratic size expression. -/
theorem detectorScale_apply (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
    detectorScale d hd h_missing i =
      ((i + 1 : ℕ) : ℝ) ^ 2 *
        (1 + C0Seq.zSize (nearGhostBase d hd h_missing i)) := by
  -- Expose the defining formula that serves as the scale's rewrite interface.
  rfl

/-- Every detector scale attached to a near-ghost base point is strictly positive. -/
theorem detectorScale_pos (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
    0 < detectorScale d hd h_missing i := by
  -- Rewrite to the product of the positive index weight and size factor.
  rw [detectorScale_apply]
  have hz : 0 ≤ C0Seq.zSize (nearGhostBase d hd h_missing i) := by
    -- Both norm summands in `zSize` are nonnegative.
    rw [C0Seq.zSize_apply]
    positivity
  -- The successor square is positive, while the size factor is at least one.
  positivity

/-- The detector scale dominates its prescribed quadratic size bound. -/
theorem quadraticSize_le_detectorScale (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
    ((i + 1 : ℕ) : ℝ) ^ 2 *
        (1 + C0Seq.zSize (nearGhostBase d hd h_missing i)) ≤
      detectorScale d hd h_missing i := by
  -- For the explicit choice of scale, the requested domination is equality.
  rw [detectorScale_apply]

/-- The detector scales attached to the near-ghost base points tend to positive infinity. -/
theorem tendsto_detectorScale (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) :
    Filter.Tendsto (detectorScale d hd h_missing) Filter.atTop Filter.atTop := by
  -- Reduce divergence to eventually exceeding an arbitrary real threshold.
  refine Filter.tendsto_atTop.2 ?_
  intro B
  obtain ⟨J, hJ⟩ := exists_nat_gt B
  have hJ_event : ∀ᶠ i : ℕ in Filter.atTop, J ≤ i :=
    Filter.eventually_ge_atTop J
  filter_upwards [hJ_event] with i hi
  -- The nonnegative size factor makes the scale dominate the successor square.
  rw [detectorScale_apply]
  have hz : 0 ≤ C0Seq.zSize (nearGhostBase d hd h_missing i) := by
    rw [C0Seq.zSize_apply]
    positivity
  -- Transport the cofinal natural bound to the reals and compare it to the square.
  have hJreal : B < (J : ℝ) := hJ
  have hi_real : (J : ℝ) ≤ i := by exact_mod_cast hi
  have hsq : (J : ℝ) ≤ (((i + 1 : ℕ) : ℝ) ^ 2) := by
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith [hi_real, sq_nonneg (i : ℝ)]
  -- Chain the threshold, quadratic, and detector-scale lower bounds.
  nlinarith [hsq, sq_nonneg (i : ℝ)]

/-- Normalizing the near-ghost base-point size by its detector scale gives a
reciprocal-square bound. -/
theorem zSize_div_detectorScale_le (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
    C0Seq.zSize (nearGhostBase d hd h_missing i) /
        detectorScale d hd h_missing i ≤
      1 / (((i + 1 : ℕ) : ℝ) ^ 2) := by
  -- Rewrite the scale so that its two positive denominator factors are visible.
  rw [detectorScale_apply]
  have hz : 0 ≤ C0Seq.zSize (nearGhostBase d hd h_missing i) := by
    rw [C0Seq.zSize_apply]
    positivity
  have hA : 0 < (((i + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hOnePos : 0 < 1 + C0Seq.zSize (nearGhostBase d hd h_missing i) := by
    linarith
  -- Clear only the proved-nonzero factors and finish the normalized inequality.
  field_simp [ne_of_gt hA, ne_of_gt hOnePos]
  nlinarith [hz]

end Lorentz
