module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Maximal

public section

namespace Lorentz

/- Theorem 7.6 (Maximal monotonicity of the ghost-curve operator) (1): the
monotone polar of the ghost-curve operator graph is the graph itself. -/
#check (Lorentz.monotonePolar_ghostCurveOperator_graph :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (_ : ∀ (w : C0Seq × L1Seq) p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w))),
    C0Seq.monotonePolar
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph =
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)

/- Theorem 7.6 (Maximal monotonicity of the ghost-curve operator) (2): the
ghost-curve operator graph is maximal among monotone subsets of `C0Seq × L1Seq`. -/
#check (Lorentz.maximalMonotone_ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (_ : ∀ (w : C0Seq × L1Seq) p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w))),
    Maximal C0Seq.coordinateDualPairing.IsMonotone
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)

end Lorentz
