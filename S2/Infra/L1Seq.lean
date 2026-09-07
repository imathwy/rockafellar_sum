/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Sequence.L1

/-!
# The `L1Seq` model and truncations

This source-facing module records coordinate evaluation, finite truncation, and
density facts for real summable sequences.
-/

/- Infrastructure A.5 (The ℓ¹ sequence model and coordinate truncations)
The real, `ℕ`-indexed `ℓ¹` model has canonical coordinate evaluation and explicit prefix
truncations with finite support; these truncations converge in norm and witness density. -/
#check (L1Seq : Type)
#check (L1Seq.norm_eq_tsum_abs : ∀ x : L1Seq, ‖x‖ = ∑' n, |x n|)
#check (lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) 1 : ℕ → L1Seq →L[ℝ] ℝ)
#check (lp.norm_apply_le_norm (E := fun _ : ℕ ↦ ℝ) (p := 1) one_ne_zero :
  ∀ (x : L1Seq) (n : ℕ), ‖x n‖ ≤ ‖x‖)
#check (L1Seq.truncate : L1Seq → ℕ → L1Seq)
#check (L1Seq.truncate_apply : ∀ (x : L1Seq) (n i : ℕ),
  L1Seq.truncate x n i = if i < n then x i else 0)
#check (L1Seq.truncate_hasFiniteSupport : ∀ (x : L1Seq) (n : ℕ),
  (fun i ↦ L1Seq.truncate x n i).HasFiniteSupport)
#check (L1Seq.tendsto_truncate : ∀ x : L1Seq,
  Filter.Tendsto (L1Seq.truncate x) Filter.atTop (nhds x))
#check (L1Seq.tendsto_norm_truncate_sub : ∀ x : L1Seq,
  Filter.Tendsto (fun n ↦ ‖L1Seq.truncate x n - x‖) Filter.atTop (nhds 0))
#check (L1Seq.finitelySupported_dense :
  Dense {x : L1Seq | (fun n ↦ x n).HasFiniteSupport})
