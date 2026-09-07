/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Topology.Sequences

/-!
# Finite injective remote matching

This source-facing module records simultaneous approximation by distinct tail
indices of a dense sequence.
-/

open Filter Topology

universe u v

/- Infrastructure B.11 (Finite injective remote matching).
A tail-dense sequence admits pairwise distinct remote indices approximating any
finite family of targets within prescribed positive tolerances. -/
#check (exists_remote_injective_matching :
  ∀ {X : Type u} [MetricSpace X] (t : ℕ → X),
    (∀ b : X, ∀ U ∈ 𝓝 b, ∀ M : ℕ, ∃ n : ℕ, M < n ∧ t n ∈ U) →
    ∀ {ι : Type v} [Finite ι] (target : ι → X) (N : ℕ) (ε : ι → ℝ),
      (∀ i, 0 < ε i) →
      ∃ index : ι → ℕ, Function.Injective index ∧
        ∀ i, N < index i ∧ dist (t (index i)) (target i) < ε i)
