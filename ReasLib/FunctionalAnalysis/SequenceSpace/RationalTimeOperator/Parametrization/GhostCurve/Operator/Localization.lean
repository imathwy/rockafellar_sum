/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Localization

/-!
# Local nonnegative energy on the ghost-curve operator graph

This module transfers the localized nonnegative quadratic-pairing estimate
from the ghost curve to its set-valued operator graph.
-/

public section

namespace Lorentz

/-- A point in the graph of the ghost-curve operator has nonnegative quadratic
pairing whenever its primal component lies in `C0Seq.localOpenUnitBall`. -/
theorem quadraticPairing_nonneg_of_mem_ghostCurveOperator
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (hNZero : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (x : C0Seq) (xstar : L1Seq)
    (h_graph :
      (x, xstar) ∈ (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (h_local : x ∈ C0Seq.localOpenUnitBall) :
    0 ≤ C0Seq.quadraticPairing (x, xstar) := by
  rw [SetValuedOperator.mem_graph] at h_graph
  rw [mem_ghostCurveOperator] at h_graph
  rw [ghostGraph_eq_preimage_graphOn] at h_graph
  rcases h_graph with ⟨z, hz, hval⟩
  rw [Set.mem_preimage, Set.mem_graphOn, embedding_apply] at hz
  have h_curve : negativeCoordinate d hd z =
      ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (positiveCoordinate d hd z) := hz.2.symm
  have h_local_z : z.1.1 ∈ C0Seq.localOpenUnitBall := by
    have hx : z.1.1 = x := by
      exact congrArg (fun p : C0Seq × L1Seq ↦ p.1) hval
    rw [hx]
    exact h_local
  have hq := ghostCurveN_quadraticPairing_nonneg_of_primal_mem_localBall
    d hd h_missing zLeft z₀ hPLeft hPZero hNLeft hNZero hLeft hZero
      h h_positive h_tendsto v hvP hvN z h_curve h_local_z
  have hzx : (z : C0Seq × L1Seq) = (x, xstar) := hval
  rw [← hzx]
  exact hq

end Lorentz
