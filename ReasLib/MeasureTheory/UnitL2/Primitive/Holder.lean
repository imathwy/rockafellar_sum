module

public import Mathlib.Topology.MetricSpace.Holder
public import ReasLib.MeasureTheory.UnitL2.Primitive

@[expose] public section

open scoped ENNReal InnerProductSpace

namespace UnitL2

/-- The primitive of a real `UnitL2` vector satisfies a square-root increment estimate on
`Set.Icc 0 1`. -/
theorem abs_primitive_sub_le (y : UnitL2) {r t : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |primitive y t - primitive y r| ≤ ‖y‖ * Real.sqrt |t - r| := by
  have hy_r : IntervalIntegrable (fun s : ℝ ↦ y s) MeasureTheory.volume 0 r := by
    -- Restrict global integrability to the initial interval ending at `r`.
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1]
    exact (integrable_coeFn y).mono_measure
      (MeasureTheory.volume.restrict_mono_set (Set.Ioc_subset_Ioc_right hr.2))
  have hy_t : IntervalIntegrable (fun s : ℝ ↦ y s) MeasureTheory.volume 0 t := by
    -- The same restriction supplies interval integrability up to `t`.
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
    exact (integrable_coeFn y).mono_measure
      (MeasureTheory.volume.restrict_mono_set (Set.Ioc_subset_Ioc_right ht.2))
  have hsubset : Set.uIoc r t ⊆ Set.Ioc (0 : ℝ) 1 := by
    -- The unordered interval between two points of `[0,1]` remains in `(0,1]`.
    intro s hs
    rw [Set.mem_uIoc] at hs
    rcases hs with ⟨hrs, hst⟩ | ⟨hts, hsr⟩
    · exact ⟨hr.1.trans_lt hrs, hst.trans ht.2⟩
    · exact ⟨ht.1.trans_lt hts, hsr.trans hr.2⟩
  have hmeas : MeasurableSet (Set.uIoc r t) := measurableSet_uIoc
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.uIoc r t) ≠ ⊤ :=
    -- Restricted Lebesgue measure is finite on every measurable subinterval.
    MeasureTheory.measure_ne_top _ _
  have hinner :
      ⟪MeasureTheory.indicatorConstLp 2 hmeas hfinite (1 : ℝ), y⟫_ℝ =
        ∫ s in Set.uIoc r t, y s ∂(MeasureTheory.volume) := by
    -- Restricting first to `(0,1]` and then to this subinterval changes no integral.
    rw [MeasureTheory.L2.inner_indicatorConstLp_one,
      MeasureTheory.Measure.restrict_restrict_of_subset hsubset]
  have htwo_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by
    norm_num
  have htwo_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by
    norm_num
  have hindicator_norm :
      ‖MeasureTheory.indicatorConstLp 2 hmeas hfinite (1 : ℝ)‖ =
        Real.sqrt |t - r| := by
    -- The indicator's squared norm is the Lebesgue length of the unordered interval.
    rw [MeasureTheory.norm_indicatorConstLp htwo_ne_zero htwo_ne_top, norm_one, one_mul,
      MeasureTheory.measureReal_def,
      MeasureTheory.Measure.restrict_eq_self MeasureTheory.volume hsubset,
      Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg (t - r))]
    norm_num [Real.sqrt_eq_rpow]
  -- Rewrite the increment as an interval integral and apply Hilbert-space Cauchy--Schwarz.
  rw [primitive_apply, primitive_apply,
    intervalIntegral.integral_interval_sub_left hy_t hy_r,
    intervalIntegral.abs_intervalIntegral_eq]
  calc
    |∫ s in Set.uIoc r t, y s ∂(MeasureTheory.volume)| =
        |⟪MeasureTheory.indicatorConstLp 2 hmeas hfinite (1 : ℝ), y⟫_ℝ| :=
      congrArg abs hinner.symm
    _ ≤ ‖MeasureTheory.indicatorConstLp 2 hmeas hfinite (1 : ℝ)‖ * ‖y‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖y‖ * Real.sqrt |t - r| := by
      rw [hindicator_norm, mul_comm]

/-- The primitive of a real `UnitL2` vector is Hölder continuous with exponent `1 / 2`
and constant `‖y‖₊` on the unit interval. -/
theorem holderOnWith_primitive (y : UnitL2) :
    HolderOnWith ‖y‖₊ (1 / 2 : NNReal) (primitive y) (Set.Icc (0 : ℝ) 1) := by
  intro r hr t ht
  have hreal :
      |primitive y r - primitive y t| ≤ ‖y‖ * Real.sqrt |r - t| :=
    -- Reverse the endpoints so the absolute differences match metric distance exactly.
    abs_primitive_sub_le y ht hr
  have hhalf : ((1 / 2 : NNReal) : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hpow_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := by
    norm_num
  -- Apply `ofReal` to the real estimate and normalize distance and square roots.
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, hhalf]
  calc
    ENNReal.ofReal |primitive y r - primitive y t| ≤
        ENNReal.ofReal (‖y‖ * Real.sqrt |r - t|) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (‖y‖₊ : ℝ≥0∞) * ENNReal.ofReal |r - t| ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_mul (norm_nonneg y), ← coe_nnnorm,
        ENNReal.ofReal_coe_nnreal, Real.sqrt_eq_rpow,
        ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (r - t)) hpow_nonneg]

/-- The primitive of a real `UnitL2` vector is continuous on `Set.Icc 0 1`. -/
theorem continuousOn_primitive (y : UnitL2) :
    ContinuousOn (primitive y) (Set.Icc (0 : ℝ) 1) := by
  have hhalf : 0 < (1 / 2 : NNReal) := by
    -- The square-root Hölder exponent is strictly positive.
    norm_num
  -- Positive-exponent Hölder continuity implies continuity on the same set.
  exact (holderOnWith_primitive y).continuousOn hhalf

end UnitL2
