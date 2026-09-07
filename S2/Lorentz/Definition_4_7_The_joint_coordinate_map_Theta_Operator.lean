module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap

#check (L1Seq.jointCoordinateMap :
  C0Seq → L1Seq →L[ℝ] C0Seq × (UnitL2 × ℝ))
#check (L1Seq.jointCoordinateMap_apply :
  ∀ (d : C0Seq) (a : L1Seq),
    L1Seq.jointCoordinateMap d a =
      (L1Seq.positiveOperator a, L1Seq.intervalCoordinateOperator a,
        C0Seq.pairingL d a))
