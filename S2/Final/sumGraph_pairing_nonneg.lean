module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.NormalCone
public import S2.Final.fixedBall_normalCone_polar_subset_Pairing

public section

open scoped Pointwise

namespace Lorentz

/- Lemma 7.13a (Sign decomposition for a point of the sum graph): every point
of the graph of the ghost-curve operator plus the normal cone of
`C0Seq.finalConstraint` has nonnegative quadratic pairing. -/
#check (Lorentz.ghostCurveSum_pairing_nonneg :
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
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (x : C0Seq) (ystar : L1Seq)
    (_ : (x, ystar) ∈
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
          C0Seq.dualPairing.normalCone C0Seq.finalConstraint).graph),
    0 ≤ C0Seq.quadraticPairing (x, ystar))

end Lorentz
