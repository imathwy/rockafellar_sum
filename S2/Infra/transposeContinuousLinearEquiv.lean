module

public import ReasLib.FunctionalAnalysis.StrongDual

public section

universe u v w

/- Infrastructure C.5 (Transpose of a continuous linear equivalence): the transpose of a
continuous linear equivalence is a continuous linear equivalence between the strong duals and is
therefore surjective. -/
#check (ContinuousLinearEquiv.dualMap_surjective :
  ∀ {𝕜 : Type u} [NormedField 𝕜]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F), Function.Surjective e.dualMap)
