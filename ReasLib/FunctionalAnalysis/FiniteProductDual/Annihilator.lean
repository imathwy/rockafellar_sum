/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.FiniteProductDual
public import Mathlib.Analysis.LocallyConvex.Polar

/-!
# Annihilators of finite-product ranges

This module records the coordinate criterion for a continuous functional to
annihilate a finite-product map range.
-/

public section

universe u v w x

namespace ContinuousLinearMap

/-- A coordinate functional on a triple product vanishes on the range of a map exactly
when the sum of its pullbacks along the three coordinate maps is zero. -/
theorem dualProdMap_mem_polarSubmodule_range_iff
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {E₁ : Type w} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {E₂ : Type x} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    (T : X →L[𝕜] (E₁ × (E₂ × 𝕜)))
    (T₁ : X →L[𝕜] E₁) (T₂ : X →L[𝕜] E₂) (T₃ : StrongDual 𝕜 X)
    (hT : ∀ a : X, T a = (T₁ a, T₂ a, T₃ a))
    (b : StrongDual 𝕜 E₁) (y : StrongDual 𝕜 E₂) (lam : 𝕜) :
    dualProdMap (b, y, lam) ∈ StrongDual.polarSubmodule 𝕜 T.range ↔
      precomp 𝕜 T₁ b + precomp 𝕜 T₂ y + lam • T₃ = 0 := by
  -- Evaluate the product functional after replacing `T a` by its three coordinates.
  have coordinateEvaluation (a : X) :
      dualProdMap (b, y, lam) ((T : X →ₗ[𝕜] E₁ × (E₂ × 𝕜)) a) =
        (precomp 𝕜 T₁ b + precomp 𝕜 T₂ y + lam • T₃) a := by
    -- Route correction: the imported wrapper is opaque, so its owner must export an
    -- application theorem before `dualProdEquiv_apply` can normalize this expression.
    have hTa : (T : X →ₗ[𝕜] E₁ × (E₂ × 𝕜)) a = (T₁ a, T₂ a, T₃ a) := hT a
    rw [hTa]
    -- Normalize the product functional and each pullback at the common source point.
    simp only [dualProdMap_apply, precomp_apply, comp_apply, add_apply, smul_apply,
      smul_eq_mul]
  -- Convert polar membership to vanishing on the range and argue pointwise in both directions.
  rw [StrongDual.mem_polarSubmodule]
  constructor
  · intro h
    ext a
    simpa only [zero_apply, ← coordinateEvaluation a] using
      h ((T : X →ₗ[𝕜] E₁ × (E₂ × 𝕜)) a)
        (LinearMap.mem_range_self (T : X →ₗ[𝕜] E₁ × (E₂ × 𝕜)) a)
  · intro h z hz
    rcases hz with ⟨a, rfl⟩
    rw [coordinateEvaluation a]
    simpa only [zero_apply] using
      congrArg (fun f : StrongDual 𝕜 X ↦ f a) h

end ContinuousLinearMap
