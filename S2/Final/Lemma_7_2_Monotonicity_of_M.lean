module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Monotone

public section

/- Lemma 7.2 (Monotonicity of $M$) (1): for two points of the ghost-curve graph,
the quadratic pairing of their difference is the difference between the squared
positive-coordinate distance and the squared negative-coordinate distance. -/
#check (Lorentz.quadraticPairing_sub_mem_ghostGraph :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v mP mQ : Lorentz.parametrizedSubspace d),
    mP.val ∈ Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v →
    mQ.val ∈ Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v →
    C0Seq.quadraticPairing (mP - mQ) =
      (Lorentz.positiveCoordinate d hd mP - Lorentz.positiveCoordinate d hd mQ) ^ 2 -
        ‖Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
              (Lorentz.positiveCoordinate d hd mP) -
            Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
              (Lorentz.positiveCoordinate d hd mQ)‖ ^ 2)

/- Lemma 7.2 (Monotonicity of $M$) (2): the ghost-curve operator is monotone
with respect to the coordinate dual pairing. -/
#check (Lorentz.isMonotone_ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
    ‖Lorentz.negativeCoordinate d hd zLeft - Lorentz.negativeCoordinate d hd z₀‖ < 1 →
    ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ) →
    ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 →
    C0Seq.coordinateDualPairing.IsMonotone
      (Lorentz.ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
