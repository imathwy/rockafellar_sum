/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

/-!
# Remote-support pairing limits

This module proves that uniformly bounded tails supported beyond their indices
pair to zero with every `C0Seq` vector.
-/

public section

open Topology

namespace C0Seq

/-- A uniformly norm-bounded sequence in `L1Seq` whose terms are supported strictly above
their indices pairs to zero with every sequence in `C0Seq`. -/
theorem pairingL_tendsto_zero_of_support_Ioi
    (c : ℕ → L1Seq) (C : ℝ)
    (h_support : ∀ n, Function.support (fun m ↦ c n m) ⊆ Set.Ioi n)
    (h_norm : ∀ n, ‖c n‖ ≤ C) (x : C0Seq) :
    Filter.Tendsto (fun n ↦ pairingL x (c n)) Filter.atTop (𝓝 0) := by
  -- A pointwise bound on the active coordinates controls the whole pairing series.
  have pairingBoundOnSupport :
      ∀ (a : L1Seq) (δ : ℝ),
        (∀ m ∈ Function.support (fun k ↦ a k), |x m| ≤ δ) →
          |pairingL x a| ≤ δ * ‖a‖ := by
    intro a δ h_coordinate
    have hOne : 0 < (1 : ENNReal).toReal := by
      norm_num
    have hAbs : HasSum (fun m : ℕ ↦ |a m|) ‖a‖ := by
      simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
        lp.hasSum_norm hOne a
    have hPairing : ‖∑' m : ℕ, x m * a m‖ ≤ δ * ‖a‖ := by
      refine tsum_of_norm_bounded (hAbs.mul_left δ) (fun m ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul]
      by_cases ham : a m = 0
      · simp only [ham, abs_zero, mul_zero, le_refl]
      · exact mul_le_mul_of_nonneg_right
          (h_coordinate m (Function.mem_support.mpr ham)) (abs_nonneg (a m))
    rw [pairingL_apply, ← Real.norm_eq_abs]
    exact hPairing
  -- The norm bound forces the scalar bound to be nonnegative, so `C + 1` is positive.
  have hC : 0 ≤ C := (norm_nonneg (c 0)).trans (h_norm 0)
  have hCOne : 0 < C + 1 := by
    linarith
  -- Choose a tail on which every coordinate of `x` is smaller than the scaled tolerance.
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  have hScaledPositive : 0 < ε / (C + 1) := div_pos hε hCOne
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp (tendsto_zero x) (ε / (C + 1)) hScaledPositive
  refine ⟨N, fun n hn ↦ ?_⟩
  have supportTailBound :
      ∀ m ∈ Function.support (fun k ↦ c n k), |x m| ≤ ε / (C + 1) := by
    intro m hm
    have hnm : n < m := h_support n hm
    have hNm : N ≤ m := hn.trans (Nat.le_of_lt hnm)
    simpa only [Real.dist_eq, sub_zero] using (hN m hNm).le
  -- Scaling by the strictly smaller factor `C < C + 1` leaves room below `ε`.
  have scaledNormBound : ε / (C + 1) * C < ε := by
    calc
      ε / (C + 1) * C < ε / (C + 1) * (C + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hScaledPositive
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hCOne)
  -- Combine the support estimate, the uniform norm bound, and the scalar calculation.
  calc
    dist (pairingL x (c n)) 0 = |pairingL x (c n)| := by
      rw [Real.dist_eq, sub_zero]
    _ ≤ ε / (C + 1) * ‖c n‖ :=
      pairingBoundOnSupport (c n) (ε / (C + 1)) supportTailBound
    _ ≤ ε / (C + 1) * C :=
      mul_le_mul_of_nonneg_left (h_norm n) hScaledPositive.le
    _ < ε := scaledNormBound

end C0Seq
