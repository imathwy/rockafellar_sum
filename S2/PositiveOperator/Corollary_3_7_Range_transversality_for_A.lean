module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Transpose.C0Range

/- Corollary 3.7 (Range transversality for $A^*$): if the reindexed transpose of
the rational-time positive operator maps `b` into the canonical image of `C0Seq`,
then `b = 0`. -/
#check (L1Seq.positiveOperator_reindexedTranspose_transverse :
  ∀ b : L1Seq,
    L1Seq.positiveOperator.reindexedTranspose b ∈ Set.range C0Seq.pairingL → b = 0)

/- Equivalently, the two ranges meet only at zero. -/
#check (L1Seq.range_positiveOperator_reindexedTranspose_inter_range_pairingL :
  Set.range L1Seq.positiveOperator.reindexedTranspose ∩ Set.range C0Seq.pairingL = {0})
