module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart

/- Lemma 3.5b (Operator-valued symmetric-part identity) -/
#check (L1Seq.positiveOperator_symmetricPart :
  C0Seq.pairingL.comp L1Seq.positiveOperator + L1Seq.positiveOperator.reindexedTranspose =
    2 • (L1Seq.intervalCoordinateAdjoint.comp L1Seq.intervalCoordinateOperator))
