module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization
public import S2.PositiveOperator.Definition_3_9_A_missing_range_vector_and_its_coordinate_functional

public section

/- Lemma 5.1 (Membership criterion for $C$): an ambient pair belongs to the
parametrized subspace exactly when its translated first coordinate belongs to
the real span of the fixed normalized vector outside the operator range. -/
#check (Lorentz.mk_mem_parametrizedSubspace_iff
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (x : C0Seq) (u : L1Seq),
    (x, u) ∈ Lorentz.parametrizedSubspace
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) ↔
      x + L1Seq.positiveOperator u ∈ ℝ ∙
        ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
