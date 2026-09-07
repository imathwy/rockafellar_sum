module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteCopySequence

#check (L1Seq.remoteDetectorDifference :
  C0Seq → ℕ → ℕ → (ℕ → L1Seq) → ℕ → L1Seq)

#check (L1Seq.remoteDetectorDifference_apply :
  ∀ (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    L1Seq.remoteDetectorDifference d p q c n = L1Seq.twoDet d p q - c n)
