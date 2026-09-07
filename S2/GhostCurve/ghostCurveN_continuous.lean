module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Continuity

public section

/- Lemma 6.18b (Compatibility and continuity at every junction) (1): the branch
formulas agree at `-1`, `0`, every left and right dyadic vertex, `3 / 2`, and `2`. -/
#check (Lorentz.ghostCurveN_neg_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d),
    Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v (-1) =
      Lorentz.negativeCoordinate d hd zLeft)

#check (Lorentz.ghostCurveN_zero :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d),
    Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 0 =
      Lorentz.negativeCoordinate d hd z₀)

#check (Lorentz.ghostCurveN_leftTime :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d) (k : ℕ),
    Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (Lorentz.leftTime k) =
      Lorentz.negativeCoordinate d hd
        (Lorentz.leftVertex d hd h_missing z₀ k))

#check (Lorentz.ghostCurveN_rightTime :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d) (i : ℕ),
    Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (DetectorTriple.rightTime i) =
      Lorentz.negativeCoordinate d hd
        (Lorentz.rightVertex d hd h_missing h h_tendsto i))

#check (Lorentz.ghostCurveN_three_halves :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d),
    Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v (3 / 2 : ℝ) =
      Lorentz.negativeCoordinate d hd
        (Lorentz.rightVertex d hd h_missing h h_tendsto 0))

#check (Lorentz.ghostCurveN_two :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d),
    Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 2 =
      (2 : ℝ) • Lorentz.negativeCoordinate d hd v)

/- Lemma 6.18b (Compatibility and continuity at every junction) (2): the curve
takes value `0` at ghost time `1`, and both dyadic vertex chains tend to `0`. -/
#check (Lorentz.ghostCurveN_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d),
    Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 1 = 0)

#check (Lorentz.leftVertex_tendsto_ghost :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)),
    Filter.Tendsto
      (fun k ↦ Lorentz.negativeCoordinate d hd
        (Lorentz.leftVertex d hd h_missing z₀ k))
      Filter.atTop (nhds 0))

#check (Lorentz.rightVertex_tendsto_ghost :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)),
    Filter.Tendsto
      (fun i ↦ Lorentz.negativeCoordinate d hd
        (Lorentz.rightVertex d hd h_missing h h_tendsto i))
      Filter.atTop (nhds 0))

/- Lemma 6.18b (Compatibility and continuity at every junction) (3): the
piecewise negative-coordinate curve is continuous on all of `ℝ`, including at
the accumulation junction `P = 1`. -/
#check (Lorentz.continuous_ghostCurveN :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d),
    Continuous (Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v))
