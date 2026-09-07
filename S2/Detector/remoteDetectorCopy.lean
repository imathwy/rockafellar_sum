module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteCopySequence
public import S2.PositiveOperator.Definition_3_9_A_missing_range_vector_and_its_coordinate_functional

/- Lemma 5.6a (Choice of a remote-copy sequence with error 1/n): for fixed
coordinates `p < q`, choose equal-norm copies of the distinguished determinant
vector, supported beyond each index and with interval-coordinate error less than
`1 / (n + 1 : ℝ)`. -/
#check (L1Seq.exists_remoteDetectorCopy
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (p q : ℕ), p < q →
    ∃ c : ℕ → L1Seq, ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ =
          ‖L1Seq.twoDet
            (ContinuousLinearMap.unitVectorOutsideRange
              L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator
              (L1Seq.twoDet
                (ContinuousLinearMap.unitVectorOutsideRange
                  L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q)‖ <
          1 / (n + 1 : ℝ))
