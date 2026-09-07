module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import ReasLib.MeasureTheory.UnitL2.Integrable

@[expose] public section

open MeasureTheory

namespace UnitL2

/-- The indefinite interval integral of a real `UnitL2` vector, based at zero. -/
noncomputable def primitive (y : UnitL2) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, y s

/-- Evaluating the primitive of a real `UnitL2` vector gives its defining interval integral. -/
@[simp]
theorem primitive_apply (y : UnitL2) (t : ℝ) :
    primitive y t = ∫ s in (0 : ℝ)..t, y s := by
  -- Unfolding the primitive exposes exactly its defining interval integral.
  rfl

/-- If all initial interval integrals of a real `UnitL2` vector vanish on `[0, 1]`,
then the vector is zero. -/
theorem eq_zero_of_primitive_eq_zero (y : UnitL2)
    (h_primitive : ∀ t ∈ Set.Icc (0 : ℝ) 1, (∫ s in (0 : ℝ)..t, y s) = 0) : y = 0 := by
  have hy : IntervalIntegrable (fun s : ℝ ↦ y s) volume 0 1 := by
    -- Integrability of the `UnitL2` representative supplies the differentiation hypothesis.
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrable_coeFn y
  -- Equality in `UnitL2` reduces to almost-everywhere equality of representatives.
  rw [Lp.eq_zero_iff_ae_eq_zero]
  let f : ℝ → ℝ := fun x ↦ y x
  change f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0
  -- Removing the null right endpoint lets us work at interior points.
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_of_ae hy.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioo] with x hx_deriv hx
  have hx_uIcc : x ∈ Set.uIcc (0 : ℝ) 1 := by
    -- An interior point belongs to the closed unordered interval used by differentiation.
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨hx.1.le, hx.2.le⟩
  have hzero_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    -- The base point zero is an endpoint of the same unordered interval.
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨le_rfl, zero_le_one⟩
  have h_integral_deriv :
      HasDerivAt (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, y s) (y x) x :=
    hx_deriv hx_uIcc 0 hzero_uIcc
  have h_integral_zero :
      (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, y s) =ᶠ[nhds x] (fun _ : ℝ ↦ 0) := by
    -- Interior points have a neighborhood on which the assumed primitive vanishes.
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact h_primitive t ⟨ht.1.le, ht.2.le⟩
  have h_zero_deriv :
      HasDerivAt (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, y s) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h_integral_zero
  -- Uniqueness of the derivative identifies the representative with zero.
  exact h_integral_deriv.unique h_zero_deriv

end UnitL2
