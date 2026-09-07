module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Gram

/- Lemma 3.3c (The Gram double series equals ‖Va‖²): the rational-time Gram
double series is the squared `UnitL2` norm of `intervalCoordinateOperator a`. -/
#check (L1Seq.gramTsum_eq_norm_intervalCoordinateOperator_sq : ∀ a : L1Seq,
    (∑' p : ℕ × ℕ,
      min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2) =
      ‖L1Seq.intervalCoordinateOperator a‖ ^ 2)
