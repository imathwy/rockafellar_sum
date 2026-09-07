/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.StrongDual

/-!
# Transpose of a continuous linear equivalence

This source-facing module records surjectivity of the dual map of a continuous
linear equivalence.
-/

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
