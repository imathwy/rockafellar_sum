/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.Localization
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Single

/-!
# Remote ball in `C0Seq`

This module defines the fixed far point and the remote convex ball used by the
ghost-curve construction.
-/

@[expose] public section

open scoped ZeroAtInfty

namespace C0Seq

/-- The point in real `c₀` whose zeroth coordinate is `4` and whose other coordinates vanish. -/
def farPoint : C₀(ℕ, ℝ) := c0Single 0 4

/-- The coordinate formula for `farPoint`. -/
theorem farPoint_apply (n : ℕ) : farPoint n = if n = 0 then 4 else 0 := by
  -- Expose the named point and use the coordinate formula for a single-coordinate sequence.
  rw [farPoint, c0Single_apply]

/-- The norm of `farPoint` is `4`. -/
theorem norm_farPoint : ‖farPoint‖ = 4 := by
  -- Reduce the norm to the absolute value of the unique nonzero coordinate.
  rw [farPoint, norm_c0Single]
  norm_num

/-- The open ball of radius `1` centered at `farPoint`. -/
def remoteBall : Set C₀(ℕ, ℝ) := Metric.ball farPoint 1

/-- Membership in `remoteBall` is strict distance less than `1` from `farPoint`. -/
theorem mem_remoteBall (x : C₀(ℕ, ℝ)) :
    x ∈ remoteBall ↔ dist x farPoint < 1 := by
  -- Unfold the named set and apply the standard metric-ball membership criterion.
  rw [remoteBall, Metric.mem_ball]

/-- The open unit ball at zero and `remoteBall` are disjoint. -/
theorem localOpenUnitBall_disjoint_remoteBall :
    Disjoint localOpenUnitBall remoteBall := by
  -- Reduce disjointness of the named balls to separation of their centers.
  unfold localOpenUnitBall remoteBall
  apply Metric.ball_disjoint_ball
  -- The center distance is four, while the two radii sum to two.
  rw [dist_zero_left, norm_farPoint]
  norm_num

/-- The set `remoteBall` is convex over `ℝ`. -/
theorem convex_remoteBall : Convex ℝ remoteBall := by
  -- Expose the named ball and use convexity of metric balls in real normed spaces.
  unfold remoteBall
  exact convex_ball farPoint 1

end C0Seq
