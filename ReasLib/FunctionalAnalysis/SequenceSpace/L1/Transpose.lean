/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import ReasLib.Analysis.Sequence.L1

/-!
# Paper transposes on `L1Seq`

This module defines precomposition transposes of continuous maps out of the
real summable-sequence space.
-/

public section

universe u v

namespace ContinuousLinearMap

/-- The transpose of a continuous linear map from `L1Seq`, defined by precomposition on
continuous linear functionals. -/
noncomputable def paperTranspose {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : L1Seq →L[ℝ] E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ L1Seq :=
  ContinuousLinearMap.precomp ℝ T

/-- Evaluating the transpose of a continuous linear map amounts to precomposing the
functional with that map. -/
@[simp]
theorem paperTranspose_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : L1Seq →L[ℝ] E) (φ : StrongDual ℝ E) (a : L1Seq) :
    T.paperTranspose φ a = φ (T a) := by
  -- Unfolding precomposition reduces evaluation to ordinary function composition.
  rfl

/-- The transpose of the sum of two continuous linear maps from `L1Seq` is the sum of
their transposes. -/
@[simp]
theorem paperTranspose_add {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S T : L1Seq →L[ℝ] E) :
    (S + T).paperTranspose = S.paperTranspose + T.paperTranspose := by
  -- Test the two transposes on a dual functional and then on a primal vector.
  ext φ a
  -- Evaluation reduces the claim to additivity of the tested functional.
  simp only [paperTranspose_apply, add_apply, map_add]

/-- Transposition of continuous linear maps from `L1Seq` reverses composition, with the
outer map acting by precomposition on continuous linear functionals. -/
@[simp]
theorem paperTranspose_comp
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : L1Seq →L[ℝ] E) (U : E →L[ℝ] F) :
    (U.comp T).paperTranspose =
      T.paperTranspose.comp (ContinuousLinearMap.precomp ℝ U) := by
  -- Test the composite transposes pointwise at both continuous-linear-map layers.
  ext φ a
  -- The computation rules identify both sides with `φ (U (T a))`.
  simp only [paperTranspose_apply, comp_apply, precomp_apply]

/-- The transpose of a real scalar multiple of a continuous linear map from `L1Seq` is
the same scalar multiple of its transpose. -/
@[simp]
theorem paperTranspose_smul {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (T : L1Seq →L[ℝ] E) :
    (c • T).paperTranspose = c • T.paperTranspose := by
  -- Test scalar compatibility on a dual functional and a primal vector.
  ext φ a
  -- Evaluation reduces the claim to real-linearity of the tested functional.
  simp only [paperTranspose_apply, smul_apply, map_smul]

end ContinuousLinearMap
