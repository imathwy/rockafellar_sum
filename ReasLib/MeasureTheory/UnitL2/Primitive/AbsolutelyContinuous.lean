module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import ReasLib.MeasureTheory.UnitL2.Primitive

@[expose] public section

open MeasureTheory

namespace UnitL2

/-- The primitive of a real `UnitL2` vector is absolutely continuous on the unit interval. -/
theorem absolutelyContinuousOnInterval_primitive (y : UnitL2) :
    AbsolutelyContinuousOnInterval (primitive y) 0 1 := by
  have hy : IntervalIntegrable (fun s : ℝ ↦ y s) volume 0 1 := by
    -- Integrability of the representative on `(0, 1]` is the controlling interval hypothesis.
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrable_coeFn y
  have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    -- The primitive is based at the left endpoint of the unordered unit interval.
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨le_rfl, zero_le_one⟩
  have hprimitive :
      primitive y = fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, y s := by
    -- Record the pointwise primitive equation at function level for stable rewriting.
    funext t
    exact primitive_apply y t
  -- Apply the canonical absolute-continuity theorem and identify its integral with the primitive.
  rw [hprimitive]
  exact hy.absolutelyContinuousOnInterval_intervalIntegral hzero

/-- The derivative of the primitive of a real `UnitL2` vector equals the vector almost
everywhere on the represented unit interval. -/
theorem ae_hasDerivAt_primitive (y : UnitL2) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), HasDerivAt (primitive y) (y t) t := by
  have hy : IntervalIntegrable (fun s : ℝ ↦ y s) volume 0 1 := by
    -- The local differentiation theorem uses the same interval-integrability invariant.
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrable_coeFn y
  have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    -- The base point zero lies in the closed unordered unit interval.
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨le_rfl, zero_le_one⟩
  have hprimitive : primitive y = fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, y s := by
    -- Lift the defining pointwise identity to an equality of functions before differentiation.
    funext t
    exact primitive_apply y t
  -- Restrict the ambient almost-everywhere result and retain membership in the
  -- represented interval.
  filter_upwards [ae_restrict_of_ae hy.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioc] with t ht_deriv ht
  have ht_uIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by
    -- Every point of `(0, 1]` also lies in the corresponding unordered closed interval.
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨ht.1.le, ht.2⟩
  -- Specialize differentiation at base point zero and normalize to `primitive y`.
  rw [hprimitive]
  exact ht_deriv ht_uIcc 0 hzero

end UnitL2
