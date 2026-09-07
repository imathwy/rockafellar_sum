module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

public section

/- Proposition 1.3 (Maximal monotonicity via the monotone polar): a monotone subset of
`C0Seq × L1Seq` is maximal among monotone subsets exactly when it equals its monotone polar. -/
#check (DualPairing.maximalMonotone_iff_polar_eq C0Seq.coordinateDualPairing :
  ∀ (S : Set (C0Seq × L1Seq)), C0Seq.coordinateDualPairing.IsMonotone S →
    (Maximal C0Seq.coordinateDualPairing.IsMonotone S ↔
      C0Seq.coordinateDualPairing.monotonePolar S = S))
