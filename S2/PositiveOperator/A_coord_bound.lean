module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator

public section

/- Lemma 3.2a (Coordinate tail estimate for A) (1): each coordinate of the
positive operator is bounded by the corresponding coordinate and twice the
strict upper absolute tail. -/
#check (L1Seq.abs_positiveOperator_apply_le :
  ∀ (a : L1Seq) (n : ℕ),
    |L1Seq.positiveOperator a n| ≤ |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0)

/- Lemma 3.2a (Coordinate tail estimate for A) (2): the explicit coordinate
majorant tends to zero. -/
#check (L1Seq.positiveOperatorCoordBound_tendsto :
  ∀ a : L1Seq,
    Filter.Tendsto
      (fun n : ℕ ↦ |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0)
      Filter.atTop (nhds 0))

/- Lemma 3.2a (Coordinate tail estimate for A) (3): the explicit coordinate
majorant is bounded uniformly by three times the `L1Seq` norm. -/
#check (L1Seq.positiveOperatorCoordBound_le :
  ∀ (a : L1Seq) (n : ℕ),
    |a n| + 2 * (∑' m : ℕ, if n < m then |a m| else 0) ≤ 3 * ‖a‖)
