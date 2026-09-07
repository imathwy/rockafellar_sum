module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator

/- Definition 3.1 (The positive operator $A$) -/
#check (L1Seq.positiveOperator : L1Seq →L[ℝ] C0Seq)
#check (L1Seq.positiveOperator_apply :
  ∀ (a : L1Seq) (n : ℕ),
    L1Seq.positiveOperator a n = rationalTime n * a n +
      2 * ∑' m : ℕ, if n < m then min (rationalTime n) (rationalTime m) * a m else 0)
