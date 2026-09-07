/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Sequence.L1.RemoteSupport

/-!
# Remote support matching

This module assigns distinct remote indices to the nonzero coordinates of a finite support.
-/

/- Lemma 2.12a (Remote matching of the support times).
For finitely supported `b : L1Seq`, its nonzero coordinates can be assigned distinct
indices beyond `N` whose rational times meet the prescribed positive tolerances. -/
#check (L1Seq.existsRemoteSupportMatching :
  ∀ (b : L1Seq), (fun i ↦ b i).HasFiniteSupport → ∀ (N : ℕ) (δ : ℕ → ℝ),
    (∀ i, b i ≠ 0 → 0 < δ i) →
    ∃ m : ℕ → ℕ, Set.InjOn m (Function.support fun i ↦ b i) ∧
      ∀ i, b i ≠ 0 → N < m i ∧ |rationalTime (m i) - rationalTime i| < δ i)
