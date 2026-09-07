/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Normalized vectors outside an operator range

This module packages the unit-norm witness supplied by a nonsurjective
continuous linear map together with its range-exclusion specification.
-/

public section

namespace ContinuousLinearMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A unit vector chosen outside the range of a nonsurjective continuous real-linear map. -/
noncomputable def unitVectorOutsideRange (f : E →L[ℝ] F)
    (h : ¬ Function.Surjective f) : F :=
  NormedSpace.normalize (Classical.choose (not_forall.mp h))

/-- Normalizing a vector outside the range of a continuous linear map keeps it outside the range. -/
private lemma normalize_not_mem_range (f : E →L[ℝ] F) {x : F}
    (hx : x ∉ Set.range f) : NormedSpace.normalize x ∉ Set.range f := by
  -- A preimage of the normalized vector would scale to a preimage of the original vector.
  intro hnormalize
  rcases hnormalize with ⟨y, hy⟩
  apply hx
  refine ⟨‖x‖ • y, ?_⟩
  calc
    f (‖x‖ • y) = ‖x‖ • f y := f.map_smul ‖x‖ y
    _ = ‖x‖ • NormedSpace.normalize x := congrArg (fun z : F ↦ ‖x‖ • z) hy
    _ = x := NormedSpace.norm_smul_normalize x

/-- The chosen unit vector is outside the map's range and has norm one. -/
theorem unitVectorOutsideRange_spec (f : E →L[ℝ] F)
    (h : ¬ Function.Surjective f) :
    unitVectorOutsideRange f h ∉ Set.range f ∧
      ‖unitVectorOutsideRange f h‖ = 1 := by
  -- Extract the witness whose lack of a preimage certifies nonsurjectivity.
  let x : F := Classical.choose (not_forall.mp h)
  have hx : x ∉ Set.range f := Classical.choose_spec (not_forall.mp h)
  -- The outside-range witness is nonzero because every linear map sends zero to zero.
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hx
    refine ⟨0, ?_⟩
    rw [f.map_zero, hzero]
  -- Normalization preserves exclusion from the range and gives the required unit norm.
  have hnormalized : NormedSpace.normalize x ∉ Set.range f :=
    normalize_not_mem_range f hx
  have hnorm : ‖NormedSpace.normalize x‖ = 1 :=
    NormedSpace.norm_normalize_eq_one_iff.mpr hx0
  simpa only [unitVectorOutsideRange, x] using And.intro hnormalized hnorm

end ContinuousLinearMap
