module

public import ReasLib.Analysis.Normed.Operator.Range
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing
public import S2.PositiveOperator.Lemma_3_8_The_range_of_A_is_proper

/- Definition 3.9 (A missing range vector and its coordinate functional) (1):
the selected vector is outside the range of `L1Seq.positiveOperator` and has norm one. -/
#check (ContinuousLinearMap.unitVectorOutsideRange_spec
    L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective :
  ContinuousLinearMap.unitVectorOutsideRange
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective ∉
      Set.range L1Seq.positiveOperator ∧
    ‖ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective‖ = 1)

/- Definition 3.9 (A missing range vector and its coordinate functional) (2):
pairing with the selected vector is its continuous coordinate functional on `L1Seq`. -/
#check (C0Seq.pairingL
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  L1Seq →L[ℝ] ℝ)
#check (C0Seq.pairingL_apply
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ a : L1Seq,
    C0Seq.pairingL
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) a =
      ∑' n : ℕ,
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) n * a n)
