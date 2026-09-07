module

public import ReasLib.Analysis.C0Seq.NormalCone.ClosedBall
public import S2.Final.fixedBall_normalCone_polar_subset_Pairing

public section

/- Lemma 7.12b (Direct maximality certificate for the fixed-ball normal cone): every
pair in the monotone polar of the normal-cone graph of `C0Seq.finalConstraint` belongs
to that graph. -/
#check (C0Seq.finalConstraint_normalCone_polar_subset :
  C0Seq.coordinateDualPairing.monotonePolar
      (C0Seq.coordinateDualPairing.normalConeGraph C0Seq.finalConstraint) ⊆
    C0Seq.coordinateDualPairing.normalConeGraph C0Seq.finalConstraint)
