module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Lipschitz

public section

/- Lemma 6.20a (Same-side Lipschitz bound by chain telescoping) (1): the
negative-coordinate curve is `1`-Lipschitz on the half-line through the ghost
time from the left. -/
#check (Lorentz.lipschitzOnWith_ghostCurveN_Iic :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖Lorentz.negativeCoordinate d hd zLeft -
      Lorentz.negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)),
    LipschitzOnWith 1
      (Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
      (Set.Iic (1 : ℝ)))

/- Lemma 6.20a (Same-side Lipschitz bound by chain telescoping) (2): the
negative-coordinate curve is `1`-Lipschitz on the half-line through the ghost
time from the right. -/
#check (Lorentz.lipschitzOnWith_ghostCurveN_Ici :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    LipschitzOnWith 1
      (Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
      (Set.Ici (1 : ℝ)))
