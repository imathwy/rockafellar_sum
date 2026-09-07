/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Lorentz past ray

This module defines the past ray through a normalized left anchor and proves
its coordinate, cone, and energy identities.
-/

public section

namespace Lorentz

/-- The past-ray point at parameter `P` based at `zLeft`. -/
@[expose]
noncomputable def pastRay (d : C0Seq) (zLeft : parametrizedSubspace d) (P : ℝ) :
    parametrizedSubspace d :=
  (-P) • zLeft

/-- A past-ray point is the scalar multiple `(-P) • zLeft`. -/
theorem pastRay_apply (d : C0Seq) (zLeft : parametrizedSubspace d) (P : ℝ) :
    pastRay d zLeft P = (-P) • zLeft := by
  -- Expose the scalar-multiple formula built into the ray construction.
  rfl

/-- The positive coordinate of a normalized past-ray point equals its parameter. -/
theorem positiveCoordinate_pastRay (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d) (hzP : positiveCoordinate d hd zLeft = -1)
    (P : ℝ) (_ : P ≤ -1) :
    positiveCoordinate d hd (pastRay d zLeft P) = P := by
  -- Push the positive coordinate through the ray scaling and use normalization.
  rw [pastRay_apply, map_smul, hzP]
  simp only [smul_eq_mul]
  -- The remaining equality is the scalar identity `(-P) * (-1) = P`.
  ring

/-- The negative coordinate of a past-ray point is the corresponding scalar
multiple of the negative coordinate of its base point. -/
theorem negativeCoordinate_pastRay (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d) (P : ℝ) :
    negativeCoordinate d hd (pastRay d zLeft P) =
      (-P) • negativeCoordinate d hd zLeft := by
  -- Linearity carries the negative coordinate through the defining scaling.
  rw [pastRay_apply, map_smul]

/-- A scalar multiple of a normalized parametrized point gives its displayed
Lorentz-coordinate point in the range of the Lorentz embedding. -/
theorem pastRay_mem_embeddingRange (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (hzP : positiveCoordinate d hd zLeft = -1) (P : ℝ) :
    (P, negativeCoordinate d hd (pastRay d zLeft P)) ∈ embeddingRange d hd := by
  -- Use the past-ray point itself as the preimage under the Lorentz embedding.
  rw [mem_embeddingRange]
  refine ⟨pastRay d zLeft P, ?_⟩
  rw [embedding_apply]
  congr 1
  -- Linearity and the normalization of `zLeft` identify the positive coordinate.
  rw [pastRay_apply, map_smul, hzP]
  simp only [smul_eq_mul]
  ring

/-- The negative coordinate of a normalized past-ray base vector has norm
strictly less than one. -/
theorem pastRay_slope_lt_one (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (hzN : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16) :
    ‖negativeCoordinate d hd zLeft‖ < 1 := by
  -- The assumed quantitative bound is strictly stronger than the unit bound.
  linarith

/-- At a past-ray scale `P ≤ -1`, the negative-coordinate norm scales by
the nonnegative factor `-P`. -/
theorem pastRay_negativeCoordinate_norm (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d) (P : ℝ) (hP : P ≤ -1) :
    ‖negativeCoordinate d hd (pastRay d zLeft P)‖ =
      (-P) * ‖negativeCoordinate d hd zLeft‖ := by
  -- The ray scale is nonnegative, so norm homogeneity has no absolute-value residue.
  have hPnonneg : 0 ≤ -P := by
    linarith
  rw [negativeCoordinate_pastRay, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hPnonneg]

/-- At a past-ray scale `P ≤ -1`, the negative-coordinate norm is below
`-P`, which is itself below `1 - P`. -/
theorem pastRay_negativeCoordinate_bounds (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (hzN : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : P ≤ -1) :
    ‖negativeCoordinate d hd (pastRay d zLeft P)‖ < -P ∧ -P < 1 - P := by
  -- Positivity of the scale lets the strict slope inequality survive multiplication.
  have hPneg : 0 < -P := by linarith
  have hslope := pastRay_slope_lt_one d hd zLeft hzN
  rw [pastRay_negativeCoordinate_norm d hd zLeft P hP]
  constructor
  · simpa only [mul_one] using mul_lt_mul_of_pos_left hslope hPneg
  -- The remaining gap is the fixed unit offset in `1 - P`.
  · linarith

/-- The Lorentz embedding of a normalized past-ray point at scale `P ≤ -1`
belongs to the past Lorentz cone. -/
theorem pastRay_mem_pastCone (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (hzP : positiveCoordinate d hd zLeft = -1)
    (hzN : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : P ≤ -1) :
    embedding d hd (pastRay d zLeft P) ∈ pastCone (HilbertProd2 UnitL2) := by
  -- Reduce cone membership to the coordinate norm inequality.
  rw [embedding_apply, mem_pastCone]
  have hbounds := pastRay_negativeCoordinate_bounds d hd zLeft hzN P hP
  -- The normalized positive coordinate is `P`, while the norm is strictly below `-P`.
  rw [positiveCoordinate_pastRay d hd zLeft hzP P hP]
  exact hbounds.1.le

/-- The Lorentz embedding of a normalized past-ray point at scale `P ≤ -1`
has nonnegative Lorentz energy. -/
theorem pastRay_energy_nonneg (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (hzP : positiveCoordinate d hd zLeft = -1)
    (hzN : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : P ≤ -1) :
    0 ≤ energy (embedding d hd (pastRay d zLeft P)) := by
  -- Canonical past-cone membership supplies nonnegativity of Lorentz energy.
  exact energy_nonneg_of_mem_pastCone
    (pastRay_mem_pastCone d hd zLeft hzP hzN P hP)

/-- A normalized past-ray point at scale `P ≤ -1` has nonnegative quadratic
pairing. -/
theorem pastRay_quadraticPairing_nonneg (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (hzP : positiveCoordinate d hd zLeft = -1)
    (hzN : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : P ≤ -1) :
    0 ≤ C0Seq.quadraticPairing (pastRay d zLeft P) := by
  -- Transfer the established energy bound through the quadratic-energy identity.
  rw [quadraticPairing_eq_energy d hd]
  simpa only [embedding_apply] using
    pastRay_energy_nonneg d hd zLeft hzP hzN P hP

end Lorentz
