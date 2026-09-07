module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart

namespace L1Seq

/- Lemma 3.7a (Transversality reduction through the symmetric-part identity):
if `positiveOperator.reindexedTranspose b = C0Seq.pairingL x`, then the symmetric-part
identity expresses `2 • intervalCoordinateAdjoint (intervalCoordinateOperator b)` as
`C0Seq.pairingL (positiveOperator b + x)`. -/
#check (L1Seq.two_smul_intervalCoordinateAdjoint_eq_pairingL :
  ∀ (b : L1Seq) (x : C0Seq),
    positiveOperator.reindexedTranspose b = C0Seq.pairingL x →
      2 • intervalCoordinateAdjoint (intervalCoordinateOperator b) =
        C0Seq.pairingL (positiveOperator b + x))

/- The corresponding symmetric-part value lies in the range of the canonical pairing. -/
#check (L1Seq.two_smul_intervalCoordinateAdjoint_mem_range :
  ∀ b : L1Seq,
    positiveOperator.reindexedTranspose b ∈ Set.range C0Seq.pairingL →
      2 • intervalCoordinateAdjoint (intervalCoordinateOperator b) ∈
        Set.range C0Seq.pairingL)

end L1Seq
