/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Sequence.L1.Relocation
public import ReasLib.Analysis.Sequence.L1.RemoteSupport
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator

/-!
# Remote relocation of interval coordinates

This module transfers finite-support relocation identities through the
interval-coordinate operator.
-/

@[expose] public section

noncomputable section

namespace L1Seq

/-- Applying the interval-coordinate operator to a scalar coordinate singleton gives the
corresponding scalar multiple of the rational interval vector. -/
private lemma intervalCoordinateOperator_apply_single_value (n : ℕ) (c : ℝ) :
    intervalCoordinateOperator (lp.single 1 n c) =
      c • UnitL2.rationalIntervalVec n := by
  -- Express the scalar singleton through the unit singleton and use linearity.
  have hSingle :
      lp.single 1 n c = c • (lp.single 1 n (1 : ℝ) : L1Seq) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : ℕ ↦ ℝ) 1 n c (1 : ℝ))
  rw [hSingle, map_smul, intervalCoordinateOperator_apply_single]

/-- The interval-coordinate synthesis difference of a finite relocation is the sum of
the relocated coordinate-vector differences. -/
private lemma intervalCoordinateOperator_remoteCopy_sub_eq_sum
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ) :
    intervalCoordinateOperator (remoteCopy b h_b m) - intervalCoordinateOperator b =
      ∑ i ∈ h_b.toFinset,
        b i • (UnitL2.rationalIntervalVec (m i) - UnitL2.rationalIntervalVec i) := by
  classical
  -- Evaluate the operator on the defining finite sum of copied coordinates.
  have hCopy :
      intervalCoordinateOperator (remoteCopy b h_b m) =
        ∑ i ∈ h_b.toFinset, b i • UnitL2.rationalIntervalVec (m i) := by
    simp only [remoteCopy, map_sum, intervalCoordinateOperator_apply_single_value]
  -- Finite support turns the infinite synthesis formula for the original vector into a sum.
  have hOriginal :
      intervalCoordinateOperator b =
        ∑ i ∈ h_b.toFinset, b i • UnitL2.rationalIntervalVec i := by
    rw [intervalCoordinateOperator_apply]
    apply tsum_eq_sum
    intro i hi
    have hbi : b i = 0 := by
      by_contra hbi
      exact hi (h_b.mem_toFinset.mpr hbi)
    simp only [hbi, zero_smul]
  -- Subtract the two finite expansions term by term and factor each coefficient.
  rw [hCopy, hOriginal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (smul_sub (b i) _ _).symm

/-- A finite weighted sum of square roots is small when every radicand is bounded by a
uniform squared tolerance determined by the total weight. -/
private lemma weightedSqrtSum_lt {ι : Type*}
    (s : Finset ι) (w d : ι → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hd : ∀ i ∈ s, d i < (ε / ((∑ j ∈ s, w j) + 1)) ^ 2) :
    ∑ i ∈ s, w i * Real.sqrt (d i) < ε := by
  classical
  let S := ∑ i ∈ s, w i
  let ρ := ε / (S + 1)
  -- Nonnegative weights make the denominator positive, hence the uniform radius is positive.
  have hS : 0 ≤ S := by
    exact Finset.sum_nonneg fun i hi ↦ hw i hi
  have hDenom : 0 < S + 1 := by
    linarith
  have hρ : 0 < ρ := div_pos hε hDenom
  have hSρ : S * ρ < ε := by
    dsimp only [ρ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hDenom).2
    nlinarith
  -- Bound each square root by the common radius, then sum the weighted inequalities.
  calc
    ∑ i ∈ s, w i * Real.sqrt (d i) ≤ ∑ i ∈ s, w i * ρ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      have hdi : d i < ρ ^ 2 := by
        simpa only [S, ρ] using hd i hi
      exact ((Real.sqrt_lt' hρ).2 hdi).le
    _ = S * ρ := by
      rw [Finset.sum_mul]
    _ < ε := hSρ

/-- The interval-coordinate synthesis error of a finite coefficient relocation is bounded by
the coefficient-weighted square-root displacement of the corresponding rational times. -/
theorem norm_intervalCoordinateOperator_remoteCopy_sub_le
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ) :
    ‖intervalCoordinateOperator (remoteCopy b h_b m) - intervalCoordinateOperator b‖ ≤
      ∑ i ∈ h_b.toFinset,
        |b i| * Real.sqrt |rationalTime (m i) - rationalTime i| := by
  -- Expose the finite synthesis difference and apply the triangle inequality.
  rw [intervalCoordinateOperator_remoteCopy_sub_eq_sum]
  refine (norm_sum_le _ _).trans_eq ?_
  -- The norm of each summand is its coefficient magnitude times the exact interval distance.
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_smul, Real.norm_eq_abs]
  unfold UnitL2.rationalIntervalVec
  rw [UnitL2.norm_sub_intervalVec]

/-- Every finitely supported coefficient vector admits an injective relocation beyond a given
index whose interval-coordinate synthesis error is smaller than any prescribed positive bound. -/
theorem exists_remoteCopy_synthesisError_lt
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ → ℕ,
      (Set.InjOn m (Function.support fun i ↦ b i) ∧
        ∀ i, b i ≠ 0 → N < m i) ∧
      ‖intervalCoordinateOperator (remoteCopy b h_b m) - intervalCoordinateOperator b‖ <
        ε := by
  -- Choose one squared tolerance small enough for every coordinate in the finite support.
  let δ := (ε / ((∑ i ∈ h_b.toFinset, |b i|) + 1)) ^ 2
  have hWeightSum : 0 ≤ ∑ i ∈ h_b.toFinset, |b i| := by
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hδ : 0 < δ := by
    have hDenom : 0 < (∑ i ∈ h_b.toFinset, |b i|) + 1 := by
      linarith
    exact sq_pos_of_pos (div_pos hε hDenom)
  obtain ⟨m, hmInjective, hm⟩ :=
    existsRemoteSupportMatching b h_b N (fun _ ↦ δ) (fun _ _ ↦ hδ)
  refine ⟨m, ⟨hmInjective, fun i hi ↦ (hm i hi).1⟩, ?_⟩
  -- Combine the synthesis estimate with the pointwise displacement guarantees.
  refine (norm_intervalCoordinateOperator_remoteCopy_sub_le b h_b m).trans_lt ?_
  apply weightedSqrtSum_lt h_b.toFinset (fun i ↦ |b i|)
    (fun i ↦ |rationalTime (m i) - rationalTime i|) ε hε
  · intro i hi
    exact abs_nonneg (b i)
  · intro i hi
    have hiNonzero : b i ≠ 0 := h_b.mem_toFinset.mp hi
    simpa only [δ] using (hm i hiNonzero).2

/-- Every finitely supported coefficient vector has an equal-norm copy supported strictly beyond
a prescribed cutoff whose interval-coordinate synthesis is arbitrarily close to the original. -/
theorem exists_remoteReplication
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ b' : L1Seq,
      Function.support (fun n ↦ b' n) ⊆ Set.Ioi N ∧
        ‖b'‖ = ‖b‖ ∧
        ‖intervalCoordinateOperator b' - intervalCoordinateOperator b‖ < ε := by
  -- Select an injective relocation whose coordinates lie past the cutoff and whose error is small.
  obtain ⟨m, ⟨hmInjective, hmTail⟩, hError⟩ :=
    exists_remoteCopy_synthesisError_lt b h_b N ε hε
  -- The remote copy has the required support and norm by the relocation interface.
  refine ⟨remoteCopy b h_b m, ?_, ?_, hError⟩
  · exact support_remoteCopy_subset_Ioi b h_b m hmInjective N hmTail
  · exact norm_remoteCopy b h_b m hmInjective

end L1Seq
