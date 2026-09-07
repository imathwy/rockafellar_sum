/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Sequence.L1
public import ReasLib.Order.RationalTime
public import ReasLib.Topology.Sequences

/-!
# Remote support matching

This module constructs injective remote assignments for finitely supported
summable sequences.
-/

namespace L1Seq

/-- A finitely supported real summable sequence admits an injective assignment of its
nonzero coordinates to sufficiently large indices with prescribed rational-time accuracy. -/
public theorem existsRemoteSupportMatching
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (N : ℕ) (δ : ℕ → ℝ)
    (hδ : ∀ i, b i ≠ 0 → 0 < δ i) :
    ∃ m : ℕ → ℕ, Set.InjOn m (Function.support fun i ↦ b i) ∧
      ∀ i, b i ≠ 0 → N < m i ∧ |rationalTime (m i) - rationalTime i| < δ i := by
  classical
  let t : ℕ → Set.Ioo (0 : ℝ) 1 :=
    fun n ↦ ⟨rationalTime n, rationalTime_mem_Ioo n⟩
  -- Every neighborhood in the unit interval contains a smaller right-hand interval,
  -- and tail density supplies a rational time in that interval beyond any threshold.
  have hTail : ∀ x : Set.Ioo (0 : ℝ) 1, ∀ U ∈ nhds x, ∀ M : ℕ,
      ∃ n : ℕ, M < n ∧ t n ∈ U := by
    intro x U hU M
    obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hU
    let η : ℝ := min (ε / 2) ((1 - x.1) / 2)
    have hηpos : 0 < η := by
      apply lt_min
      · linarith
      · have hxUpper := x.property.2
        linarith
    have hηeps : η < ε := by
      have hηle := min_le_left (ε / 2) ((1 - x.1) / 2)
      linarith
    have hηunit : x.1 + η < 1 := by
      have hηle := min_le_right (ε / 2) ((1 - x.1) / 2)
      have hxUpper := x.property.2
      linarith
    have hInterval : Set.Ioo x.1 (x.1 + η) ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨x.property.1.trans hy.1, hy.2.trans hηunit⟩
    obtain ⟨n, hnM, hnInterval⟩ :=
      exists_gt_rationalTime_mem_Ioo (lt_add_of_pos_right x.1 hηpos) hInterval M
    refine ⟨n, hnM, hBall ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    rw [abs_of_pos (sub_pos.mpr hnInterval.1)]
    linarith [hnInterval.2]
  -- Local instance justification (finite support subtype): the matching API requires
  -- the finite support instance supplied by `h_b`.
  letI : Finite (Function.support fun i ↦ b i) := h_b.to_subtype
  -- Match all support coordinates at once, retaining injectivity and both pointwise bounds.
  obtain ⟨index, hIndexInjective, hIndex⟩ :=
    exists_remote_injective_matching t hTail
      (fun i : Function.support fun i ↦ b i ↦
        ⟨rationalTime i.1, rationalTime_mem_Ioo i.1⟩)
      N (fun i ↦ δ i.1) (fun i ↦ hδ i.1 i.property)
  let m : ℕ → ℕ := fun i ↦ if hi : b i ≠ 0 then index ⟨i, hi⟩ else 0
  refine ⟨m, ?_, ?_⟩
  · -- On the support, the total assignment agrees with the injective subtype assignment.
    intro i hi j hj hij
    have hiNonzero : b i ≠ 0 := hi
    have hjNonzero : b j ≠ 0 := hj
    have hmi : m i = index ⟨i, hi⟩ := by
      simp only [m, dif_pos hiNonzero]
    have hmj : m j = index ⟨j, hj⟩ := by
      simp only [m, dif_pos hjNonzero]
    have hIndexEq : index ⟨i, hi⟩ = index ⟨j, hj⟩ :=
      hmi.symm.trans (hij.trans hmj)
    exact congrArg Subtype.val (hIndexInjective hIndexEq)
  · -- Erase the subtype distance and read off the threshold and accuracy estimates.
    intro i hi
    have hiBounds := hIndex ⟨i, hi⟩
    constructor
    · simpa only [m, dif_pos hi] using hiBounds.1
    · simpa only [m, dif_pos hi, t, Subtype.dist_eq, Real.dist_eq] using hiBounds.2

end L1Seq
