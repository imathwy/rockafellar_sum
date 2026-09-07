module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.ProperRange

/- Lemma 3.8b (Transpose-surjectivity contradicts A* transversality):
`L1Seq.positiveOperator` is not surjective. -/
#check (L1Seq.positiveOperator_not_surjective :
  ¬ Function.Surjective L1Seq.positiveOperator)
