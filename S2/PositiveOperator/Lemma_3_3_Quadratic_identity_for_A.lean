module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.QuadraticIdentity

#check (L1Seq.positiveOperator_quadratic_eq_gramTsum :
  ∀ a : L1Seq,
    C0Seq.pairingL (L1Seq.positiveOperator a) a =
      ∑' p : ℕ × ℕ,
        min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2)

/- Lemma 3.3 (Quadratic identity for $A$) -/
#check (L1Seq.positiveOperator_quadratic_eq_norm_sq :
  ∀ a : L1Seq,
    C0Seq.pairingL (L1Seq.positiveOperator a) a =
      ‖L1Seq.intervalCoordinateOperator a‖ ^ 2)
