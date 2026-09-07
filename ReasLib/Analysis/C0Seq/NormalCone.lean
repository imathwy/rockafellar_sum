/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.Localization
public import ReasLib.Analysis.Convex.NormalCone
public import ReasLib.Analysis.Sequence.L1

/-!
# Normal cone on `C0Seq`

This module specializes normal-cone domain, origin, and pairing facts to the
fixed closed-ball constraint on real `C0Seq`.
-/

public section

open scoped Pointwise ZeroAtInfty

namespace C0Seq

/-- The domain of the normal cone of the closed radius-`1 / 2` ball in real `c₀`
is the ball itself. -/
theorem normalConeDom_finalConstraint (P : DualPairing C₀(ℕ, ℝ) L1Seq) :
    P.normalConeDom finalConstraint = finalConstraint := by
  -- Specialize the generic domain identity to the fixed closed-ball constraint.
  exact DualPairing.dom_normalCone P finalConstraint

/-- The normal cone of the closed radius-`1 / 2` ball in real `c₀` at zero is the
singleton containing zero. -/
theorem normalCone_finalConstraint_zero (P : DualPairing C₀(ℕ, ℝ) L1Seq) :
    P.normalCone finalConstraint (0 : C₀(ℕ, ℝ)) = {0} := by
  -- Reduce the normal-cone computation to zero's established interior membership.
  apply DualPairing.normalCone_eq_zero_of_mem_interior P
  exact zero_mem_interior_finalConstraint

/-- If zero belongs to the graph of an operator plus the normal cone of the
closed radius-`1 / 2` ball in real `c₀`, then zero belongs to the graph of the
operator. -/
theorem zero_mem_graph_of_mem_add_normalCone
    (P : DualPairing C₀(ℕ, ℝ) L1Seq)
    (M : SetValuedOperator C₀(ℕ, ℝ) L1Seq)
    (h_zero : (0, 0) ∈ (M + P.normalCone finalConstraint).graph) :
    (0, 0) ∈ M.graph := by
  rw [SetValuedOperator.mem_graph_add] at h_zero
  rw [SetValuedOperator.mem_graph] at ⊢
  rcases h_zero with ⟨m, hm, n, hn, hmn⟩
  rw [normalCone_finalConstraint_zero P] at hn
  have hnzero : n = 0 := by simpa using hn
  have hmzero : m = 0 := by simpa [hnzero] using hmn
  simpa [hmzero] using hm

end C0Seq
