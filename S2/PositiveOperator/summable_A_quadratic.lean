module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Quadratic

/- Lemma 3.3a (Absolute summability of the A quadratic expansion) (1):
the diagonal scalar series in `⟨positiveOperator a, a⟩` is absolutely summable. -/
#check (L1Seq.summable_abs_positiveOperator_diagonal :
  ∀ a : L1Seq, Summable (fun n : ℕ ↦ |rationalTime n * (a n) ^ 2|))

/- Lemma 3.3a (Absolute summability of the A quadratic expansion) (2):
the outer strict-upper scalar series in `⟨positiveOperator a, a⟩` is absolutely summable. -/
#check (L1Seq.summable_abs_positiveOperator_offDiagonal :
  ∀ a : L1Seq, Summable (fun n : ℕ ↦
    |(2 * ∑' m : ℕ,
      if n < m then min (rationalTime n) (rationalTime m) * a m else 0) * a n|))

/- Lemma 3.3a (Absolute summability of the A quadratic expansion) (3):
the full product-indexed rational-time kernel series is absolutely summable. -/
#check (L1Seq.summable_abs_positiveOperator_kernel :
  ∀ a : L1Seq, Summable (fun p : ℕ × ℕ ↦
    |min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2|))
