module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

public section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The continuous dual of `E × (F × 𝕜)` is continuously linearly equivalent to the
product of the coordinate duals, with the last dual identified with `𝕜`. -/
def dualProdEquiv :
    (StrongDual 𝕜 E × (StrongDual 𝕜 F × 𝕜)) ≃L[𝕜] StrongDual 𝕜 (E × (F × 𝕜)) :=
  ((ContinuousLinearEquiv.refl 𝕜 (StrongDual 𝕜 E)).prodCongr
      (((ContinuousLinearEquiv.refl 𝕜 (StrongDual 𝕜 F)).prodCongr
          (toSpanSingletonCLE : 𝕜 ≃L[𝕜] StrongDual 𝕜 𝕜)).trans
        (coprodEquivL 𝕜 :
          (StrongDual 𝕜 F × StrongDual 𝕜 𝕜) ≃L[𝕜] StrongDual 𝕜 (F × 𝕜)))).trans
    (coprodEquivL 𝕜 :
      (StrongDual 𝕜 E × StrongDual 𝕜 (F × 𝕜)) ≃L[𝕜]
        StrongDual 𝕜 (E × (F × 𝕜)))

/-- The continuous linear map that sums three coordinate functionals on `E × (F × 𝕜)`. -/
def dualProdMap :
    StrongDual 𝕜 E × (StrongDual 𝕜 F × 𝕜) →L[𝕜] StrongDual 𝕜 (E × (F × 𝕜)) :=
  dualProdEquiv.toContinuousLinearMap

/-- The continuous linear map that restricts a functional to the three coordinate
inclusions, identifying the last restriction with a scalar. -/
def dualProdCoords :
    StrongDual 𝕜 (E × (F × 𝕜)) →L[𝕜] StrongDual 𝕜 E × (StrongDual 𝕜 F × 𝕜) :=
  dualProdEquiv.symm.toContinuousLinearMap

/-- The coordinate decomposition followed by its sum recovers the original functional. -/
theorem dualProdMap_dualProdCoords (L : StrongDual 𝕜 (E × (F × 𝕜))) :
    dualProdMap (dualProdCoords L) = L := by
  exact dualProdEquiv.apply_symm_apply L

/-- Applying `dualProdEquiv` evaluates and sums its three coordinate functionals. -/
theorem dualProdEquiv_apply (p : StrongDual 𝕜 E × (StrongDual 𝕜 F × 𝕜))
    (x : E) (y : F) (t : 𝕜) :
    dualProdEquiv p (x, y, t) = p.1 x + p.2.1 y + p.2.2 * t := by
  -- Reduce the two coproduct equivalences, then normalize the resulting scalar sum.
  simp [dualProdEquiv, add_assoc, mul_comm]

/-- Applying `dualProdMap` evaluates and sums its three coordinate functionals. -/
theorem dualProdMap_apply (p : StrongDual 𝕜 E × (StrongDual 𝕜 F × 𝕜))
    (x : E) (y : F) (t : 𝕜) :
    dualProdMap p (x, y, t) = p.1 x + p.2.1 y + p.2.2 * t := by
  -- Expose only the public wrapper and reuse the equivalence's computation rule.
  simpa only [dualProdMap, ContinuousLinearEquiv.coe_apply] using
    dualProdEquiv_apply p x y t

/-- The inverse of `dualProdEquiv` restricts to the three coordinate inclusions. -/
theorem dualProdEquiv_symm_apply (L : StrongDual 𝕜 (E × (F × 𝕜))) :
    dualProdEquiv.symm L =
      (L.comp (inl 𝕜 E (F × 𝕜)),
        L.comp ((inr 𝕜 E (F × 𝕜)).comp (inl 𝕜 F 𝕜)), L (0, 0, 1)) := by
  -- Reduce to coordinate restrictions and reassociate the nested composition canonically.
  simp [dualProdEquiv, comp_assoc]

/-- Every real continuous linear functional on `E × (F × ℝ)` has a unique triple of
coordinate functionals whose evaluations sum to the original functional. -/
theorem existsUnique_dualProd {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : StrongDual ℝ (E × (F × ℝ))) :
    ∃! p : StrongDual ℝ E × (StrongDual ℝ F × ℝ),
      ∀ x y t, L (x, y, t) = p.1 x + p.2.1 y + p.2.2 * t := by
  -- The inverse equivalence supplies the canonical coordinate triple.
  refine ⟨dualProdEquiv.symm L, ?_, ?_⟩
  · intro x y t
    calc
      L (x, y, t) = dualProdEquiv (dualProdEquiv.symm L) (x, y, t) := by
        rw [dualProdEquiv.apply_symm_apply]
      _ = (dualProdEquiv.symm L).1 x + (dualProdEquiv.symm L).2.1 y +
          (dualProdEquiv.symm L).2.2 * t := dualProdEquiv_apply _ _ _ _
  · intro q hq
    -- Equality after reconstruction determines the coordinate triple by injectivity.
    apply dualProdEquiv.injective
    apply ContinuousLinearMap.ext
    intro z
    rcases z with ⟨x, y, t⟩
    calc
      dualProdEquiv q (x, y, t) = q.1 x + q.2.1 y + q.2.2 * t :=
        dualProdEquiv_apply _ _ _ _
      _ = L (x, y, t) := (hq x y t).symm
      _ = dualProdEquiv (dualProdEquiv.symm L) (x, y, t) := by
        rw [dualProdEquiv.apply_symm_apply]

end ContinuousLinearMap
