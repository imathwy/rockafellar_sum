module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Quadratic

/- Lemma 3.3b (Triangle symmetrization of the kernel series): the diagonal plus twice
the strict-upper-triangle kernel sum is the full symmetric double series. -/
#check (L1Seq.positiveOperator_diag_add_two_upper_eq_kernel : ∀ a : L1Seq,
  (∑' n : ℕ, rationalTime n * (a n) ^ 2) +
      2 * (∑' n : ℕ, ∑' m : ℕ,
        if n < m then min (rationalTime n) (rationalTime m) * a n * a m else 0) =
    ∑' p : ℕ × ℕ,
      min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2)
