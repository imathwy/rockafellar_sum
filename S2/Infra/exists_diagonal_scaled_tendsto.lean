/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.Group.Sequences

/-!
# Diagonal Scaled Convergence

This module exposes diagonal selection lemmas for norm-null sequences and scales.
-/

public section

open Filter

universe u

/- Infrastructure E.2 (Diagonal selection after adaptive scaling) (1): after fixing a
positive scale, a norm-null sequence has an arbitrarily late term below any positive
scaled tolerance. -/
#check (exists_ge_scaled_norm_lt :
  ∀ {E : Type u} [SeminormedAddGroup E]
    (u : ℕ → E) (_ : Tendsto u atTop (nhds 0)) (scale ε : ℝ)
    (_ : 0 < scale) (_ : 0 < ε) (i : ℕ),
    ∃ n, i ≤ n ∧ scale * ‖u n‖ < ε)

/- Infrastructure E.2 (Diagonal selection after adaptive scaling) (2): positive scale
and tolerance schedules have a strictly increasing diagonal choice satisfying every
scheduled threshold and scaled norm bound. -/
#check (exists_diagonal_scaled_tendsto :
  ∀ {E : Type u} [SeminormedAddGroup E]
    (u : ℕ → E) (_ : Tendsto u atTop (nhds 0)) (scale ε : ℕ → ℝ)
    (_ : ∀ i, 0 < scale i) (_ : ∀ i, 0 < ε i),
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ i, i ≤ n i ∧ scale i * ‖u (n i)‖ < ε i)
