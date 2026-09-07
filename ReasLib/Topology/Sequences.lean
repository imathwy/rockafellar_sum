/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Tail-dense sequence extraction

This module records strictly increasing subsequence extraction from a
tail-dense sequence in a metric space.
-/

public section

open Filter Topology

universe u v

/-- If a sequence in a metric space visits every neighborhood strictly after every
index, then each point is the limit of a strictly increasing subsequence. -/
theorem exists_strictMono_subseq_tendsto
    {X : Type u} [MetricSpace X] (x : ℕ → X)
    (h_tail : ∀ b : X, ∀ U ∈ 𝓝 b, ∀ N : ℕ, ∃ n : ℕ, N < n ∧ x n ∈ U)
    (a : X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  -- Turn the strict tail-visit hypothesis into the cluster-point condition.
  apply MapClusterPt.tendsto_subseq
  rw [mapClusterPt_iff_frequently]
  intro U hU
  rw [frequently_atTop']
  exact h_tail a U hU

/-- A tail-visiting sequence enters every positive metric ball beyond any threshold. -/
private lemma exists_index_gt_dist_lt_of_tail_visit
    {X : Type u} [MetricSpace X] (t : ℕ → X)
    (h_tail : ∀ b : X, ∀ U ∈ 𝓝 b, ∀ M : ℕ, ∃ n : ℕ, M < n ∧ t n ∈ U)
    (b : X) (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, M < n ∧ dist (t n) b < ε := by
  -- Apply the tail hypothesis to the prescribed metric ball.
  obtain ⟨n, hn, hnt⟩ := h_tail b (Metric.ball b ε) (Metric.ball_mem_nhds b hε) M
  exact ⟨n, hn, Metric.mem_ball.mp hnt⟩

/-- A finite ordinal family of targets admits distinct remote approximating indices. -/
private lemma exists_injective_fin_approximation
    {X : Type u} [MetricSpace X] (t : ℕ → X)
    (h_tail : ∀ b : X, ∀ U ∈ 𝓝 b, ∀ M : ℕ, ∃ n : ℕ, M < n ∧ t n ∈ U) :
    ∀ (k : ℕ) (target : Fin k → X) (N : ℕ) (ε : Fin k → ℝ),
      (∀ i, 0 < ε i) →
      ∃ index : Fin k → ℕ, Function.Injective index ∧
        ∀ i, N < index i ∧ dist (t (index i)) (target i) < ε i := by
  intro k
  induction k with
  | zero =>
      intro target N ε hε
      -- There are no targets, so the unique empty assignment has every required property.
      exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ k ih =>
      intro target N ε hε
      -- Choose the head index, then recursively place every tail index strictly beyond it.
      obtain ⟨head, hNhead, hhead⟩ :=
        exists_index_gt_dist_lt_of_tail_visit t h_tail (target 0) N (ε 0) (hε 0)
      obtain ⟨tailIndex, htailInjective, htail⟩ :=
        ih (fun i ↦ target i.succ) head (fun i ↦ ε i.succ) (fun i ↦ hε i.succ)
      refine ⟨Fin.cons head tailIndex, ?_, ?_⟩
      · -- Strict separation from the recursive range makes the combined assignment injective.
        apply Fin.cons_injective_of_injective
        · intro hheadRange
          obtain ⟨i, rfl⟩ := hheadRange
          exact (Nat.lt_irrefl _ (htail i).1)
        · exact htailInjective
      · -- The threshold and approximation bounds hold at the head and on the recursive tail.
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa only [Fin.cons_zero] using And.intro hNhead hhead
        · exact ⟨lt_trans hNhead (htail j).1, (htail j).2⟩

/-- A sequence that visits every neighborhood after every threshold admits an
injective finite assignment of remote indices approximating prescribed targets. -/
theorem exists_remote_injective_matching
    {X : Type u} [MetricSpace X] (t : ℕ → X)
    (h_tail : ∀ b : X, ∀ U ∈ 𝓝 b, ∀ M : ℕ, ∃ n : ℕ, M < n ∧ t n ∈ U)
    {ι : Type v} [Finite ι] (target : ι → X) (N : ℕ) (ε : ι → ℝ)
    (hε : ∀ i, 0 < ε i) :
    ∃ index : ι → ℕ, Function.Injective index ∧
      ∀ i, N < index i ∧ dist (t (index i)) (target i) < ε i := by
  -- Enumerate the finite target type and solve the resulting finite ordinal problem.
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨finIndex, hfinInjective, hfin⟩ :=
    exists_injective_fin_approximation t h_tail k (target ∘ e.symm) N (ε ∘ e.symm)
      (fun i ↦ hε (e.symm i))
  -- Transport the injective assignment and its pointwise bounds back along the equivalence.
  refine ⟨finIndex ∘ e, hfinInjective.comp e.injective, ?_⟩
  intro i
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hfin (e i)
