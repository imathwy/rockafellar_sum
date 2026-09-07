/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.Group.Approximation

/-!
# Nonzero vectors under half-norm perturbations

This module exposes elementary norm estimates preserving a nonzero coordinate
under controlled approximation.
-/

public section

universe u

/- Lemma 6.2a (Approximation preserving a nonzero N-coordinate) (1) -/
#check (ne_zero_of_dist_lt_half_norm :
  ∀ {E : Type u} [NormedAddGroup E] (nbar n : E),
    nbar ≠ 0 → dist n nbar < ‖nbar‖ / 2 → n ≠ 0)

/- Lemma 6.2a (Approximation preserving a nonzero N-coordinate) (2) -/
#check (half_norm_lt_norm_of_dist_lt_half_norm :
  ∀ {E : Type u} [NormedAddGroup E] (nbar n : E),
    nbar ≠ 0 → dist n nbar < ‖nbar‖ / 2 → ‖nbar‖ / 2 < ‖n‖)

/- Lemma 6.2a (Approximation preserving a nonzero N-coordinate) (3) -/
#check (norm_lt_three_halves_of_dist_lt_half_norm :
  ∀ {E : Type u} [NormedAddGroup E] (nbar n : E),
    nbar ≠ 0 → dist n nbar < ‖nbar‖ / 2 → ‖n‖ < 3 * ‖nbar‖ / 2)
