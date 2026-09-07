module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Polar.Rigidity

public section

/- Lemma 7.4 (Same-time rigidity away from the ghost): a polar point of the
ghost-curve operator graph whose positive coordinate is not the ghost time
belongs to that graph. -/
#check (Lorentz.mem_ghostCurveOperator_of_polar_ne_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd zLeft = -1)
    (_ : Lorentz.positiveCoordinate d hd z₀ = 0)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (_ : Lorentz.positiveCoordinate d hd v = 1)
    (w : Lorentz.parametrizedSubspace d)
    (_ : w.val ∈ C0Seq.monotonePolar
      (Lorentz.ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (_ : Lorentz.positiveCoordinate d hd w ≠ 1),
    w.val ∈
      (Lorentz.ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
