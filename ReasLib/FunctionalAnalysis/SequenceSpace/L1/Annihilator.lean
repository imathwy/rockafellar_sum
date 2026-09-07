/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.FiniteProductDual.Annihilator
public import ReasLib.FunctionalAnalysis.SequenceSpace.L1.Transpose

/-!
# Product-range annihilators on `L1Seq`

This module specializes the finite-product annihilator criterion to summable
sequence maps.
-/

public section

universe u v

namespace ContinuousLinearMap

/-- A coordinate functional on a triple product vanishes on the range of a map from
`L1Seq` exactly when the sum of the transposed coordinate functionals is zero. -/
theorem annihilates_prodRange_iff
    {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {E₂ : Type v} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (T : L1Seq →L[ℝ] (E₁ × (E₂ × ℝ)))
    (T₁ : L1Seq →L[ℝ] E₁) (T₂ : L1Seq →L[ℝ] E₂) (T₃ : StrongDual ℝ L1Seq)
    (hT : ∀ a : L1Seq, T a = (T₁ a, T₂ a, T₃ a))
    (b : StrongDual ℝ E₁) (y : StrongDual ℝ E₂) (lam : ℝ) :
    dualProdMap (b, y, lam) ∈ StrongDual.polarSubmodule ℝ T.range ↔
      T₁.paperTranspose b + T₂.paperTranspose y + lam • T₃ = 0 := by
  -- Normalize the complete transpose sum pointwise through the exported evaluation API.
  have transposeSum_eq_precomp :
      T₁.paperTranspose b + T₂.paperTranspose y + lam • T₃ =
        precomp ℝ T₁ b + precomp ℝ T₂ y + lam • T₃ := by
    ext a
    simp only [paperTranspose_apply, precomp_apply, comp_apply, add_apply, smul_apply]
  -- Rewrite to the generic product criterion, which already proves annihilation on the range.
  rw [transposeSum_eq_precomp]
  exact dualProdMap_mem_polarSubmodule_range_iff T T₁ T₂ T₃ hT b y lam

end ContinuousLinearMap
