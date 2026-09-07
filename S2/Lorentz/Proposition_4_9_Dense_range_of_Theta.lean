module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.DenseRange

public section

/- Proposition 4.9 (Dense range of $\Theta$): the joint-coordinate map associated to any vector
outside the range of the positive operator has dense range. -/
#check (L1Seq.jointCoordinateMap_denseRange :
  (d : C0Seq) → d ∉ Set.range L1Seq.positiveOperator →
    DenseRange (L1Seq.jointCoordinateMap d))
