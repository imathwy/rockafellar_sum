/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.L1.Annihilator
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Transpose

/-!
# Product-Range Annihilators

This module exposes the annihilator criterion for maps into a triple product.
-/

public section

universe u v

/- Infrastructure C.8 (Annihilator equation for a map into a triple product):
the functional with coordinates `(b, y, λ)` annihilates the range of `T` exactly when
the corresponding linear combination of its coordinate transposes is zero. -/
#check (ContinuousLinearMap.annihilates_prodRange_iff :
  ∀ {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {E₂ : Type v} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T : L1Seq →L[ℝ] (E₁ × (E₂ × ℝ)))
    (T₁ : L1Seq →L[ℝ] E₁) (T₂ : L1Seq →L[ℝ] E₂) (T₃ : StrongDual ℝ L1Seq)
    (_ : ∀ a : L1Seq, T a = (T₁ a, T₂ a, T₃ a))
    (b : StrongDual ℝ E₁) (y : StrongDual ℝ E₂) (lam : ℝ),
    ContinuousLinearMap.dualProdMap (b, y, lam) ∈
        StrongDual.polarSubmodule ℝ T.range ↔
      T₁.paperTranspose b + T₂.paperTranspose y + lam • T₃ = 0)
