module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization
public import S2.PositiveOperator.Definition_3_9_A_missing_range_vector_and_its_coordinate_functional

/- Definition 4.1 (The parametrized subspace $C$) (1): the map `Ψ` sends `(a, t)`
to `(-L1Seq.positiveOperator a + t • d, a)` for the normalized vector `d` fixed
outside the range of `L1Seq.positiveOperator`. -/
#check (Lorentz.parametrization_apply
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (a : L1Seq) (t : ℝ),
    Lorentz.parametrization
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) (a, t) =
      (-L1Seq.positiveOperator a +
        t • ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective, a))

/- Definition 4.1 (The parametrized subspace $C$) (2): the subspace `C` consists
exactly of the values of the parametrization at the normalized vector fixed outside
the range of `L1Seq.positiveOperator`. -/
#check (Lorentz.mem_parametrizedSubspace
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ z : C0Seq × L1Seq,
    z ∈ Lorentz.parametrizedSubspace
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) ↔
      ∃ a : L1Seq, ∃ t : ℝ,
        z = (-L1Seq.positiveOperator a +
          t • ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective, a))
