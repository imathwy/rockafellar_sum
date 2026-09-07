module

public import S2.Detector.Definition_5_2_Two_coordinate_determinant_vectors

/- Lemma 5.3 (Basic properties of $b_{pq}$) (1): the selected vector pairs to zero
with each of its two-coordinate determinant vectors. -/
#check (C0Seq.pairingL_twoDet_self
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ p q : ℕ, p < q →
    C0Seq.pairingL
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
        (L1Seq.twoDet
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q) = 0)

/- Lemma 5.3 (Basic properties of $b_{pq}$) (2): every two-coordinate determinant
vector of the selected unit vector has `L1Seq` norm at most two. -/
#check (L1Seq.norm_twoDet_le_two_of_norm_eq_one
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
    (ContinuousLinearMap.unitVectorOutsideRange_spec
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective).2 :
  ∀ p q : ℕ, p < q →
    ‖L1Seq.twoDet
      (ContinuousLinearMap.unitVectorOutsideRange
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q‖ ≤ 2)
