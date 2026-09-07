module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint.C0Range

/- Corollary 3.6 (Range transversality for $V^*$): if the adjoint image of
`y : UnitL2` belongs to the canonical image of `C0Seq`, then `y = 0`. -/
#check (L1Seq.intervalCoordinateAdjoint_transverse : ∀ (y : UnitL2),
  L1Seq.intervalCoordinateAdjoint y ∈ Set.range C0Seq.pairingL → y = 0)
