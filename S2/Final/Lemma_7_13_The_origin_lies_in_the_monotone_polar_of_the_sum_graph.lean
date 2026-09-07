module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.NormalCone

public section

open scoped Pointwise

/- Lemma 7.13 (The origin lies in the monotone polar of the sum graph): the
origin belongs to the monotone polar of the graph of the ghost-curve operator
plus the normal cone of `C0Seq.finalConstraint`. -/
#check (Lorentz.zero_mem_monotonePolar_ghostCurveSum :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd zLeft = -1)
    (_ : Lorentz.positiveCoordinate d hd z₀ = 0)
    (_ : ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (_ : zLeft.1.1 ∈ C0Seq.remoteBall)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd v = 1)
    (_ : ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    (0, 0) ∈ C0Seq.monotonePolar
      ((Lorentz.ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
        C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph))
