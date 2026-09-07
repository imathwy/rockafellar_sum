module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.TwoCoordinateDeterminant
public import S2.PositiveOperator.Definition_3_9_A_missing_range_vector_and_its_coordinate_functional

/- Definition 5.2 (Two-coordinate determinant vectors): for the vector `d : C0Seq`
selected in Definition 3.9 and source coordinates `p < q`, `L1Seq.twoDet d p q` is
`d p · e_q - d q · e_p` in `L1Seq`. Lean coordinates are zero-based: Lean index `k`
represents source index `k + 1`. -/
#check ((fun (p q : ℕ) (_ : p < q) ↦
    L1Seq.twoDet
      (ContinuousLinearMap.unitVectorOutsideRange
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q) :
  ∀ p q : ℕ, p < q → L1Seq)

#check (L1Seq.twoDet_apply
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ p q n : ℕ,
    L1Seq.twoDet
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q n =
      (if q = n then
          ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective p
        else 0) -
        (if p = n then
          ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective q
        else 0))
