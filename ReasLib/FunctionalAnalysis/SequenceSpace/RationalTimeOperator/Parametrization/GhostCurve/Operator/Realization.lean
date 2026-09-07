/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph.Realization

/-!
# Ghost-curve operator realization

This module transfers graph realization results to the associated set-valued
operator domain.
-/

public section

namespace Lorentz

/-- The primal coordinate of twice a normalized future-ray base point belongs
to the domain of the associated ghost-curve operator. -/
theorem two_smul_primal_mem_ghostCurveOperator_dom
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1) :
      ((2 : ℝ) • v).1.1 ∈
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).dom := by
  rw [SetValuedOperator.mem_dom]
  refine ⟨((2 : ℝ) • v).1.2, ?_⟩
  rw [mem_ghostCurveOperator]
  exact two_smul_mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v hvP

end Lorentz
