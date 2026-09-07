/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Approximation near a nonzero point

This module records lower and upper norm bounds for points within half the
norm of a nonzero reference point.
-/

public section

universe u

/-- The norm of a point strictly within half the norm of a nonzero reference point
is strictly greater than half the reference norm. -/
theorem half_norm_lt_norm_of_dist_lt_half_norm {E : Type u} [NormedAddGroup E]
    (nbar n : E) (_ : nbar ≠ 0) (hdist : dist n nbar < ‖nbar‖ / 2) :
    ‖nbar‖ / 2 < ‖n‖ := by
  -- Route correction: use the metric triangle inequality, which does not require commutativity.
  have htriangle : ‖nbar‖ ≤ dist n nbar + ‖n‖ := by
    simpa only [dist_zero_right, dist_comm nbar n] using dist_triangle nbar n 0
  -- The strict distance bound then forces the claimed lower norm bound.
  linarith

/-- A point strictly within half the norm of a nonzero reference point is nonzero. -/
theorem ne_zero_of_dist_lt_half_norm {E : Type u} [NormedAddGroup E]
    (nbar n : E) (hnbar : nbar ≠ 0) (hdist : dist n nbar < ‖nbar‖ / 2) :
    n ≠ 0 := by
  -- The reference norm is positive, and the preceding estimate bounds `‖n‖` below.
  have hnbar_pos : 0 < ‖nbar‖ := norm_pos_iff.mpr hnbar
  have hlower : ‖nbar‖ / 2 < ‖n‖ :=
    half_norm_lt_norm_of_dist_lt_half_norm nbar n hnbar hdist
  have hn_pos : 0 < ‖n‖ := by
    linarith
  -- Positive norm is equivalent to nonzeroness in a normed additive group.
  exact norm_pos_iff.mp hn_pos

/-- The norm of a point strictly within half the norm of a nonzero reference point
is strictly less than three halves of the reference norm. -/
theorem norm_lt_three_halves_of_dist_lt_half_norm {E : Type u} [NormedAddGroup E]
    (nbar n : E) (_ : nbar ≠ 0) (hdist : dist n nbar < ‖nbar‖ / 2) :
    ‖n‖ < 3 * ‖nbar‖ / 2 := by
  -- Route correction: the metric triangle inequality applies to a noncommutative normed group.
  have htriangle : ‖n‖ ≤ dist n nbar + ‖nbar‖ := by
    simpa only [dist_zero_right] using dist_triangle n nbar 0
  -- Combining it with the strict half-norm radius gives the upper estimate.
  linarith
