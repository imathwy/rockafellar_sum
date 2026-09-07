module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorScale

public section

/- Lemma 6.10a (Scaling chosen after the base point): for each near-ghost base
point, the detector scale has the prescribed quadratic formula and properties. -/
#check (Lorentz.detectorScale :
  (d : C0Seq) → d ≠ 0 →
    d ∉ Set.range L1Seq.positiveOperator → ℕ → ℝ)

/- The detector scale evaluates to its prescribed quadratic size expression. -/
#check (Lorentz.detectorScale_apply :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ),
    Lorentz.detectorScale d hd h_missing i =
      ((i + 1 : ℕ) : ℝ) ^ 2 *
        (1 + C0Seq.zSize (Lorentz.nearGhostBase d hd h_missing i)))

/- Every chosen detector scale is strictly positive. -/
#check (Lorentz.detectorScale_pos :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ),
    0 < Lorentz.detectorScale d hd h_missing i)

/- The detector scale dominates the prescribed quadratic size bound. -/
#check (Lorentz.quadraticSize_le_detectorScale :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ),
    ((i + 1 : ℕ) : ℝ) ^ 2 *
        (1 + C0Seq.zSize (Lorentz.nearGhostBase d hd h_missing i)) ≤
      Lorentz.detectorScale d hd h_missing i)

/- The chosen detector scales tend to positive infinity. -/
#check (Lorentz.tendsto_detectorScale :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator),
    Filter.Tendsto (Lorentz.detectorScale d hd h_missing)
      Filter.atTop Filter.atTop)

/- The normalized base-point size satisfies the reciprocal-square bound. -/
#check (Lorentz.zSize_div_detectorScale_le :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ),
    C0Seq.zSize (Lorentz.nearGhostBase d hd h_missing i) /
        Lorentz.detectorScale d hd h_missing i ≤
      1 / (((i + 1 : ℕ) : ℝ) ^ 2))
