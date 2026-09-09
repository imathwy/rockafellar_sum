/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedComparisons

/-!
# Assembly of the S3 monotone seed

The detector sequence is fixed. Only the two source witnesses remain parameters.
-/

public section

open Filter Topology

namespace Lorentz

/-- The full source seed with the actual scheduled detector points. -/
def assembledSeed (z v : parametrizedSubspace axisDirection) : Set (C0Seq × L1Seq) :=
  {w | (∃ p : ℝ, p ≤ 1 / 2 ∧ w = (z + p • v : parametrizedSubspace axisDirection)) ∨
    (∃ n : ℕ, w = (seedPoint n : C0Seq × L1Seq)) ∨
    w = ((2 : ℝ) • v : parametrizedSubspace axisDirection)}

/-- The full seed polar is contained in the carrier. -/
theorem assembledSeed_polar_subset_carrier (z v : parametrizedSubspace axisDirection) :
    C0Seq.monotonePolar (assembledSeed z v) ⊆ parametrizedSubspace axisDirection := by
  apply polar_subset_axisCarrier_of_seedPoint_mem
  intro n
  exact Or.inr (Or.inl ⟨n, rfl⟩)

/-- A Lorentz norm comparison implies nonnegative ambient difference pairing. -/
theorem seed_pairing_nonneg_of_norm_bound (a b : parametrizedSubspace axisDirection)
    (h : ‖negativeCoordinate axisDirection seed_axis_ne_zero a -
      negativeCoordinate axisDirection seed_axis_ne_zero b‖ ≤
      |positiveCoordinate axisDirection seed_axis_ne_zero a -
        positiveCoordinate axisDirection seed_axis_ne_zero b|) :
    0 ≤ C0Seq.quadraticPairing ((a : C0Seq × L1Seq) - (b : C0Seq × L1Seq)) := by
  rw [← Submodule.coe_sub, quadraticIdentity axisDirection seed_axis_ne_zero, map_sub, map_sub]
  have hs := (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mpr h
  rw [sq_abs] at hs
  linarith

/-- The source's five pair comparisons assemble into full seed monotonicity. -/
theorem assembledSeed_isMonotone (z v : parametrizedSubspace axisDirection)
    (hzP : positiveCoordinate axisDirection seed_axis_ne_zero z = 0)
    (hvP : positiveCoordinate axisDirection seed_axis_ne_zero v = 1)
    (hzN : ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ ≤ 1 / 64)
    (hvN : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64) :
    C0Seq.coordinateDualPairing.IsMonotone (assembledSeed z v) := by
  have hhalf (p q : ℝ) : 0 ≤ C0Seq.quadraticPairing
      (((z + p • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) -
        (z + q • v : parametrizedSubspace axisDirection)) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_add, map_smul, hzP, hvP, smul_eq_mul, mul_one, zero_add] using
      seed_halfLine_pair_bound z v hvN p q
  have hhd (p : ℝ) (hp : p ≤ 1 / 2) (n : ℕ) : 0 ≤ C0Seq.quadraticPairing
      (((z + p • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) - seedPoint n) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_add, map_smul, hzP, hvP, smul_eq_mul, mul_one, zero_add,
      positiveCoordinate_seedPoint] using seed_halfLine_detector_bound z v hzN hvN p hp n
  have hha (p : ℝ) (hp : p ≤ 1 / 2) : 0 ≤ C0Seq.quadraticPairing
      (((z + p • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) -
        ((2 : ℝ) • v : parametrizedSubspace axisDirection)) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_add, map_smul, hzP, hvP, smul_eq_mul, mul_one, zero_add] using
      seed_halfLine_anchor_bound z v hzN hvN p hp
  have hda (n : ℕ) : 0 ≤ C0Seq.quadraticPairing
      ((seedPoint n : C0Seq × L1Seq) - ((2 : ℝ) • v : parametrizedSubspace axisDirection)) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_smul, hvP, smul_eq_mul, mul_one, positiveCoordinate_seedPoint] using
      seed_detector_anchor_bound v hvN n
  apply (C0Seq.coordinateDualPairing.isMonotone_iff_subset_polar _).2
  intro a ha
  rw [C0Seq.coordinateDualPairing.mem_monotonePolar]
  intro b hb
  rw [← C0Seq.quadraticPairing_eq_coordinateQuadratic]
  rcases ha with ⟨p, hp, rfl⟩ | ⟨i, rfl⟩ | rfl
  · rcases hb with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ | rfl
    · exact hhalf p q
    · exact hhd p hp j
    · exact hha p hp
  · rcases hb with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ | rfl
    · rw [C0Seq.quadraticPairing.map_sub]
      exact hhd q hq i
    · exact quadraticPairing_seedPoint_sub_nonneg i j
    · exact hda i
  · rcases hb with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ | rfl
    · rw [C0Seq.quadraticPairing.map_sub]
      exact hha q hq
    · rw [C0Seq.quadraticPairing.map_sub]
      exact hda j
    · simp

/-- Compatibility with the scheduled points forces the limiting Lorentz cone
bound and hence the source right-side energy lower bound. -/
theorem seedPoint_polar_energy_lower_bound (w : parametrizedSubspace axisDirection)
    (hw : ∀ n, 0 ≤ C0Seq.quadraticPairing
      ((w : C0Seq × L1Seq) - (seedPoint n : C0Seq × L1Seq))) :
    2 * positiveCoordinate axisDirection seed_axis_ne_zero w - 1 ≤
      C0Seq.quadraticPairing w := by
  have hineq (n : ℕ) :
      ‖negativeCoordinate axisDirection seed_axis_ne_zero w -
        negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n)‖ ^ 2 ≤
      (positiveCoordinate axisDirection seed_axis_ne_zero w - seedTime n) ^ 2 := by
    have h := hw n
    rw [← Submodule.coe_sub, quadraticIdentity axisDirection seed_axis_ne_zero,
      map_sub, map_sub, positiveCoordinate_seedPoint] at h
    linarith
  have hcN : Tendsto (fun _ : ℕ ↦ negativeCoordinate axisDirection seed_axis_ne_zero w)
      atTop (𝓝 (negativeCoordinate axisDirection seed_axis_ne_zero w)) := tendsto_const_nhds
  have hcP : Tendsto (fun _ : ℕ ↦ positiveCoordinate axisDirection seed_axis_ne_zero w)
      atTop (𝓝 (positiveCoordinate axisDirection seed_axis_ne_zero w)) := tendsto_const_nhds
  have hN := ((hcN.sub negativeCoordinate_seedPoint_tendsto_zero).norm).pow 2
  have hP := (hcP.sub seedTime_tendsto_one).pow 2
  have hlim := le_of_tendsto_of_tendsto' hN hP hineq
  simp only [sub_zero] at hlim
  rw [quadraticIdentity axisDirection seed_axis_ne_zero]
  nlinarith

end Lorentz
