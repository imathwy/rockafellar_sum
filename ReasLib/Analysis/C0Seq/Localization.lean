module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

@[expose] public section

open scoped Pointwise ZeroAtInfty

namespace C0Seq

/-- The open unit ball centered at zero in the real space `C₀(ℕ, ℝ)`. -/
def localOpenUnitBall : Set C₀(ℕ, ℝ) := Metric.ball 0 1

/-- Membership in the open unit ball in real `c₀` is strict unit-norm boundedness. -/
theorem mem_localOpenUnitBall (x : C₀(ℕ, ℝ)) :
    x ∈ localOpenUnitBall ↔ ‖x‖ < 1 := by
  -- Normalize membership in the zero-centered metric ball to the norm inequality.
  rw [localOpenUnitBall, mem_ball_zero_iff]

/-- The open unit ball in real `c₀` is open. -/
theorem isOpen_localOpenUnitBall : IsOpen localOpenUnitBall := by
  -- Expose the defining metric ball and use its standard openness property.
  unfold localOpenUnitBall
  exact Metric.isOpen_ball

/-- The closed ball of radius `1 / 2` centered at zero in real `c₀`. -/
def finalConstraint : Set C₀(ℕ, ℝ) := Metric.closedBall 0 (1 / 2)

/-- Membership in the closed radius-`1 / 2` ball is norm boundedness by `1 / 2`. -/
theorem mem_finalConstraint (x : C₀(ℕ, ℝ)) :
    x ∈ finalConstraint ↔ ‖x‖ ≤ (1 / 2 : ℝ) := by
  -- Normalize membership in the zero-centered closed ball to the norm bound.
  rw [finalConstraint, mem_closedBall_zero_iff]

/-- The closed radius-`1 / 2` ball in real `c₀` is nonempty. -/
theorem nonempty_finalConstraint : Set.Nonempty finalConstraint := by
  -- Use zero as a point of the constraint and reduce membership to its norm bound.
  refine ⟨0, ?_⟩
  rw [mem_finalConstraint]
  norm_num

/-- The closed radius-`1 / 2` ball in real `c₀` is closed. -/
theorem isClosed_finalConstraint : IsClosed finalConstraint := by
  -- Expose the defining closed ball and apply its standard closedness property.
  unfold finalConstraint
  exact Metric.isClosed_closedBall

/-- The closed radius-`1 / 2` ball in real `c₀` is convex over `ℝ`. -/
theorem convex_finalConstraint : Convex ℝ finalConstraint := by
  -- Expose the defining closed ball and apply convexity of normed-space balls.
  unfold finalConstraint
  exact convex_closedBall 0 (1 / 2)

/-- Zero lies in the interior of the closed radius-`1 / 2` ball in real `c₀`. -/
theorem zero_mem_interior_finalConstraint :
    (0 : C₀(ℕ, ℝ)) ∈ interior finalConstraint := by
  -- Enter the interior through the open ball with the same center and radius.
  unfold finalConstraint
  apply Metric.ball_subset_interior_closedBall
  -- The center belongs to that open ball because its radius is positive.
  apply Metric.mem_ball_self
  norm_num

/-- The closed radius-`1 / 2` ball is contained in the open unit ball. -/
theorem finalConstraint_subset_localOpenUnitBall :
    finalConstraint ⊆ localOpenUnitBall := by
  -- Reduce the set inclusion to the two norm characterizations.
  intro x hx
  rw [mem_finalConstraint] at hx
  rw [mem_localOpenUnitBall]
  -- The radius `1 / 2` bound is strictly below the unit radius.
  linarith

/-- The closed radius-`1 / 2` ball is one half of the closed unit ball in real `c₀`. -/
theorem finalConstraint_eq_smul_closedUnitBall :
    finalConstraint = (1 / 2 : ℝ) • Metric.closedBall (0 : C₀(ℕ, ℝ)) 1 := by
  -- Orient the canonical nonnegative rescaling identity toward the named constraint set.
  unfold finalConstraint
  symm
  apply smul_unitClosedBall_of_nonneg
  -- Verify the scalar radius is nonnegative.
  norm_num

end C0Seq
