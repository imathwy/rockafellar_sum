/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Strong-dual transposes

This module defines the continuous-linear equivalence induced on strong duals
and its evaluation and surjectivity bridges.
-/

public section

universe u v w x

namespace ContinuousLinearEquiv

variable {𝕜 : Type u} [NormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type x} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The transpose equivalence on strong duals induced by a continuous linear equivalence. -/
def dualMap (e : E ≃L[𝕜] F) : StrongDual 𝕜 F ≃L[𝕜] StrongDual 𝕜 E :=
  e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)

/-- Evaluating `e.dualMap φ` amounts to precomposing `φ` with `e`. -/
theorem dualMap_apply (e : E ≃L[𝕜] F) (φ : StrongDual 𝕜 F) (x : E) :
    e.dualMap φ x = φ (e x) := by
  -- Unfold the transpose once; `arrowCongr_apply` identifies it with precomposition by `e`.
  simp only [dualMap, arrowCongr_apply, refl_apply, symm_symm_apply]

attribute [simp] dualMap_apply

/-- The inverse of the transpose equivalence is the transpose of the inverse equivalence. -/
theorem dualMap_symm (e : E ≃L[𝕜] F) :
    e.dualMap.symm = e.symm.dualMap := by
  -- Inverting `arrowCongr` reverses both equivalences, yielding the transpose of `e.symm`.
  simp only [dualMap, arrowCongr_symm, symm_symm, refl_symm]

attribute [simp] dualMap_symm

/-- Transposition reverses composition of continuous linear equivalences. -/
theorem dualMap_trans (e : E ≃L[𝕜] F) (f : F ≃L[𝕜] G) :
    f.dualMap.trans e.dualMap = (e.trans f).dualMap := by
  -- Evaluate both equivalences pointwise; each side is precomposition by `f ∘ e`.
  ext φ x
  simp only [trans_apply, dualMap_apply]

attribute [simp] dualMap_trans

/-- The transpose equivalence on strong duals is surjective. -/
theorem dualMap_surjective (e : E ≃L[𝕜] F) : Function.Surjective e.dualMap := by
  -- Surjectivity is part of the bundled continuous linear equivalence API.
  exact e.dualMap.surjective

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- An injective continuous linear map is not surjective when its transpose intersects the
range of an injective map into the strong dual only at zero. -/
theorem not_surjective_of_transpose_transverse
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]
    (A : E →L[ℝ] F) (J : F →L[ℝ] StrongDual ℝ E)
    (hA : Function.Injective A) (hJ : Function.Injective J)
    (h_transverse : ∀ b : StrongDual ℝ F,
      (ContinuousLinearMap.precomp ℝ A) b ∈ Set.range J → b = 0) :
    ¬ Function.Surjective A := by
  classical
  -- A hypothetical surjection is a Banach-space isomorphism because `A` is also injective.
  intro hsurjective
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hA
  have hrange : A.range = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  let e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective A hker hrange
  -- Pull a nonzero vector through the surjective transpose of this isomorphism.
  obtain ⟨x, hx⟩ := exists_ne (0 : F)
  obtain ⟨b, hb⟩ := e.dualMap_surjective (J x)
  -- The transpose used in the hypothesis is pointwise the same as `e.dualMap`.
  have hprecomp : (ContinuousLinearMap.precomp ℝ A) b = e.dualMap b := by
    ext y
    simp only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.dualMap_apply, e, ContinuousLinearEquiv.coeFn_ofBijective]
  -- Thus `b` meets the transverse range, so it must vanish.
  have hwitness : (ContinuousLinearMap.precomp ℝ A) b = J x := hprecomp.trans hb
  have hmem : (ContinuousLinearMap.precomp ℝ A) b ∈ Set.range J := ⟨x, hwitness.symm⟩
  have hbzero : b = 0 := h_transverse b hmem
  -- Injectivity of `J` then forces the chosen nonzero vector to be zero.
  have hJx : J x = J 0 := by
    calc
      J x = e.dualMap b := hb.symm
      _ = e.dualMap 0 := congrArg e.dualMap hbzero
      _ = 0 := map_zero e.dualMap
      _ = J 0 := (map_zero J).symm
  exact hx (hJ hJx)

end ContinuousLinearMap
