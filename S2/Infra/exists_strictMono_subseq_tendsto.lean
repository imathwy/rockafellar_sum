/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Topology.Sequences

/-!
# Strictly increasing convergent subsequences

This source-facing module records the canonical subsequence extraction result
for a tail-dense sequence.
-/

public section

open Filter Topology

universe u

/- Infrastructure B.10 (Increasing tail subsequences from a tail-dense enumeration)
-/
#check (exists_strictMono_subseq_tendsto :
  ∀ {X : Type u} [MetricSpace X] (x : ℕ → X),
    (∀ b : X, ∀ U ∈ 𝓝 b, ∀ N : ℕ, ∃ n : ℕ, N < n ∧ x n ∈ U) →
    ∀ a : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a))
