module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.Kernel

public section

#check (Lorentz.parameters_eq_zero_of_negativeCoordinate_eq_zero :
  ∀ (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ),
    Lorentz.negativeCoordinate d hd (Lorentz.parametrizedPoint d a t) = 0 →
      a = 0 ∧ t = 0)

/- Lemma 4.12a (Zero N-coordinate forces zero P-coordinate). -/
#check (Lorentz.positiveCoordinate_eq_zero_of_negativeCoordinate_eq_zero :
  ∀ (d : C0Seq) (hd : d ≠ 0) (z : Lorentz.parametrizedSubspace d),
    Lorentz.negativeCoordinate d hd z = 0 → Lorentz.positiveCoordinate d hd z = 0)
