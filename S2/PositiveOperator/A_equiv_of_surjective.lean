module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Equiv

/- Lemma 3.8a (Surjectivity would make A a continuous linear equivalence) -/
#check (L1Seq.positiveOperatorEquivOfSurjective :
  Function.Surjective L1Seq.positiveOperator → L1Seq ≃L[ℝ] C0Seq)

#check (L1Seq.positiveOperatorEquivOfSurjective_toContinuousLinearMap :
  ∀ h_surjective : Function.Surjective L1Seq.positiveOperator,
    (L1Seq.positiveOperatorEquivOfSurjective h_surjective).toContinuousLinearMap =
      L1Seq.positiveOperator)
