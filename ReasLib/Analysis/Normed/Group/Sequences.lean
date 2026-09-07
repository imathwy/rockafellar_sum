/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Quantitative norm-null sequence extraction

This module provides late-index, diagonal, and limiting norm estimates for
sequences converging to zero.
-/

public section

open Filter

universe u

/-- After fixing a positive scale, a norm-null sequence has an arbitrarily late term
whose scaled norm is below any prescribed positive tolerance. -/
theorem exists_ge_scaled_norm_lt {E : Type u} [SeminormedAddGroup E]
    (u : ℕ → E) (hu : Tendsto u atTop (nhds 0)) (scale ε : ℝ)
    (hscale : 0 < scale) (hε : 0 < ε) (i : ℕ) :
    ∃ n, i ≤ n ∧ scale * ‖u n‖ < ε := by
  -- Apply convergence at the positive radius obtained by dividing by the fixed scale.
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp hu) (ε / scale) (div_pos hε hscale)
  -- The maximum lies beyond both requested thresholds, so its norm has the desired bound.
  refine ⟨max i N, Nat.le_max_left i N, (lt_div_iff₀' hscale).mp ?_⟩
  simpa only [dist_zero_right] using hN (max i N) (Nat.le_max_right i N)

/-- Positive scale and tolerance schedules for a norm-null sequence have a strictly
increasing diagonal choice satisfying every scheduled threshold and scaled norm bound. -/
theorem exists_diagonal_scaled_tendsto {E : Type u} [SeminormedAddGroup E]
    (u : ℕ → E) (hu : Tendsto u atTop (nhds 0)) (scale ε : ℕ → ℝ)
    (hscale : ∀ i, 0 < scale i) (hε : ∀ i, 0 < ε i) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ i, i ≤ n i ∧ scale i * ‖u (n i)‖ < ε i := by
  -- Recast the arbitrarily late estimate as a frequent predicate for every schedule index.
  have hfrequent : ∀ j, ∃ᶠ k in atTop, scale j * ‖u k‖ < ε j :=
    fun j ↦ frequently_atTop.mpr fun threshold ↦
      exists_ge_scaled_norm_lt u hu (scale j) (ε j) (hscale j) (hε j) threshold
  -- Simultaneous extraction supplies one strictly increasing choice satisfying all predicates.
  obtain ⟨n, hn, hbound⟩ := extraction_forall_of_frequently hfrequent
  refine ⟨n, hn, ?_⟩
  intro i
  constructor
  · -- Strict growth forces the chosen index to dominate its schedule index.
    exact hn.le_apply
  · exact hbound i

/-- A fixed point is zero if its squared distance from samples of a continuous map
is bounded by the squared distance of their parameters from an anchor where the map vanishes. -/
theorem eq_zero_of_tendsto_sq_norm_bound {E : Type u} [NormedAddGroup E] {a : ℝ}
    (f : ℝ → E) (N : E) (P : ℕ → ℝ) (hf : ContinuousAt f a) (hf_a : f a = 0)
    (hP : Tendsto P atTop (nhds a)) (hP_ne : ∀ k, P k ≠ a)
    (h_bound : ∀ k, P k ≠ a →
      0 ≤ (a - P k) ^ 2 - ‖N - f (P k)‖ ^ 2) :
    N = 0 := by
  have hfp : Tendsto (fun k => f (P k)) atTop (nhds 0) := by
    have hcomp : Tendsto (fun k => f (P k)) atTop (nhds (f a)) :=
      hf.tendsto.comp hP
    simpa [hf_a] using hcomp
  have hfp_norm : Tendsto (fun k => ‖f (P k)‖) atTop (nhds 0) := by
    simpa only [norm_zero] using hfp.norm
  have hdiff : Tendsto (fun k => a - P k) atTop (nhds 0) := by
    have hconst : Tendsto (fun _k : ℕ => a) atTop (nhds a) := tendsto_const_nhds
    simpa using hconst.sub hP
  have habs : Tendsto (fun k => |a - P k|) atTop (nhds 0) := by
    simpa only [abs_zero] using hdiff.abs
  have hnorm_bound : ∀ k, ‖N - f (P k)‖ ≤ |a - P k| := by
    intro k
    have hsq := h_bound k (hP_ne k)
    have hsq' : ‖N - f (P k)‖ ^ 2 ≤ |a - P k| ^ 2 := by
      nlinarith [sq_abs (a - P k)]
    exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hsq'
  have hdiff_zero : Tendsto (fun k => N - f (P k)) atTop (nhds 0) := by
    exact squeeze_zero_norm' (Filter.Eventually.of_forall hnorm_bound) habs
  have hsum_zero : Tendsto
      (fun k => ‖N - f (P k)‖ + ‖f (P k)‖) atTop (nhds 0) := by
    have hdiff_norm : Tendsto (fun k => ‖N - f (P k)‖) atTop (nhds 0) := by
      simpa only [norm_zero] using hdiff_zero.norm
    simpa only [zero_add, add_zero] using hdiff_norm.add hfp_norm
  have hN_le (k : ℕ) :
      ‖N‖ ≤ ‖N - f (P k)‖ + ‖f (P k)‖ := by
    calc
      ‖N‖ = ‖(N - f (P k)) + f (P k)‖ := by rw [sub_add_cancel]
      _ ≤ ‖N - f (P k)‖ + ‖f (P k)‖ := norm_add_le _ _
  have hN_nonpos : ‖N‖ ≤ 0 := by
    exact ge_of_tendsto hsum_zero (Filter.Eventually.of_forall hN_le)
  have hN_norm : ‖N‖ = 0 := le_antisymm hN_nonpos (norm_nonneg N)
  exact norm_eq_zero.mp hN_norm
