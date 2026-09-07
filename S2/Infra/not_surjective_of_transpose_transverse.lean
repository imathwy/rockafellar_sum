module

public import ReasLib.FunctionalAnalysis.StrongDual

universe u v

/- Infrastructure C.6 (A proper-range criterion from transpose transversality): if the
continuous transpose of an injective continuous linear map meets the range of an injective map
into the strong dual only at zero, then the original map is not surjective. -/
#check (ContinuousLinearMap.not_surjective_of_transpose_transverse :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (A : E →L[ℝ] F) (J : F →L[ℝ] StrongDual ℝ E),
    Function.Injective A → Function.Injective J →
      (∀ b : StrongDual ℝ F,
        (ContinuousLinearMap.precomp ℝ A) b ∈ Set.range J → b = 0) →
      ¬ Function.Surjective A)
