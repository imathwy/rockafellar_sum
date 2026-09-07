module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive

public section

/- Lemma 6.16a (Fixed-time choice of the future-ray vector): there is a point of
`Lorentz.parametrizedSubspace d` with positive coordinate `1`, negative coordinate
of norm less than `1 / 16`, and first ambient coordinate of norm less than `1 / 8`. -/
#check (Lorentz.exists_futureRayBase :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (_ : d ∉ Set.range L1Seq.positiveOperator),
    ∃ v : Lorentz.parametrizedSubspace d,
      Lorentz.positiveCoordinate d hd v = 1 ∧
      ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 ∧
      ‖(v : C0Seq × L1Seq).1‖ < (1 : ℝ) / 8)
