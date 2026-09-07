module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.NormalCone

open scoped Pointwise

public section

namespace Lorentz

/- Theorem 7.15 (Failure of maximality of the sum): the graph of the ghost-curve
operator plus the normal cone of `C0Seq.finalConstraint` is not maximally monotone;
the origin lies in its monotone polar but not in the graph. -/
#check (Lorentz.not_maximalMonotone_ghostCurveSum :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (_ : zLeft.1.1 ∈ C0Seq.remoteBall)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (_ : (z₀ : C0Seq × L1Seq) ∈
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (_ : C0Seq.quadraticPairing z₀ < 0)
    (_ : C0Seq.coordinateDualPairing.IsMonotone
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph),
    ¬ Maximal C0Seq.coordinateDualPairing.IsMonotone
      ((ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
        C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph))

end Lorentz
