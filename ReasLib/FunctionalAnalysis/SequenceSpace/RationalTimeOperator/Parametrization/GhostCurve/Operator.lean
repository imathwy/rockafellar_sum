/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.SetValuedOperator
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph

/-!
# Ghost-curve set-valued operator

This module turns the ambient ghost-curve graph into a set-valued operator and
exposes its graph bridge.
-/

public section

namespace Lorentz

variable (d : C0Seq) (hd : d ≠ 0)
variable (h_missing : d ∉ Set.range L1Seq.positiveOperator)
variable (zLeft z₀ : parametrizedSubspace d)
variable (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
variable (h_tendsto : ∀ p q (h_pq : p < q),
  Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
    Filter.atTop (nhds 0))
variable (v : parametrizedSubspace d)

/-- The set-valued ghost-curve operator obtained by taking the fibers of
`ghostGraph`. -/
noncomputable def ghostCurveOperator : SetValuedOperator C0Seq L1Seq :=
  fun x ↦ {xstar | (x, xstar) ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v}

/-- Membership in the ghost-curve operator is membership in the corresponding
graph fiber. -/
@[simp]
lemma mem_ghostCurveOperator (x : C0Seq) (xstar : L1Seq) :
    xstar ∈ ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v x ↔
      (x, xstar) ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
  rfl

/-- The relation-valued graph of the ghost-curve operator is `ghostGraph`. -/
theorem graph_ghostCurveOperator :
    (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph =
      ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
  ext p
  rcases p with ⟨x, xstar⟩
  rw [SetValuedOperator.mem_graph, mem_ghostCurveOperator]

end Lorentz
