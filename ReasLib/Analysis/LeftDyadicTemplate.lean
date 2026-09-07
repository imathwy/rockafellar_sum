module

public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

open Filter Topology

namespace Lorentz

/-- The zero-based sequence of dyadic times approaching `1` from the left. -/
noncomputable def leftTime (k : ℕ) : ℝ :=
  1 - (2 : ℝ) ^ (-(k + 1 : ℝ))

/-- The defining formula for the left dyadic time sequence. -/
theorem leftTime_def (k : ℕ) :
    leftTime k = 1 - (2 : ℝ) ^ (-(k + 1 : ℝ)) := by
  -- Unfolding exposes exactly the defining dyadic formula.
  rfl

/-- The affine template obtained by scaling a vector by `1 - P`. -/
noncomputable def leftTemplate {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (N₀ : E) (P : ℝ) : E :=
  (1 - P) • N₀

/-- Evaluation of the affine left template. -/
theorem leftTemplate_apply {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (N₀ : E) (P : ℝ) :
    leftTemplate N₀ P = (1 - P) • N₀ := by
  -- The template evaluates by its defining scalar action.
  rfl

/-- The gap between successive zero-based left dyadic times. -/
theorem leftTime_succ_sub (k : ℕ) :
    leftTime (k + 1) - leftTime k = (2 : ℝ) ^ (-(k + 2 : ℝ)) := by
  -- Normalize both indices to the exponent of the smaller dyadic term.
  rw [leftTime, leftTime]
  have he : (-(↑(k + 1) + 1 : ℝ)) = -(k + 2 : ℝ) := by
    norm_num
    ring
  have hpow : (-(↑k + 1 : ℝ)) = (-(k + 2 : ℝ)) + 1 := by
    ring
  have htwo : (0 : ℝ) < 2 := by
    norm_num
  -- Splitting off the final exponent `1` reduces the gap to a ring identity.
  rw [he, hpow, Real.rpow_add htwo]
  norm_num
  ring

/-- The left dyadic time sequence converges to `1`. -/
theorem tendsto_leftTime :
    Tendsto leftTime atTop (𝓝 1) := by
  -- The affine exponent tends to `-∞` along the natural-number filter.
  have hplus : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun k : ℕ ↦ -((k : ℝ) + 1)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hplus
  -- Powers of a base greater than one therefore vanish at these exponents.
  have hrpowComp :
      (fun x : ℝ ↦ (2 : ℝ) ^ x) ∘ (fun k : ℕ ↦ -((k : ℝ) + 1)) =
        fun k : ℕ ↦ (2 : ℝ) ^ (-(k + 1 : ℝ)) := by
    funext k
    rfl
  have hpow : Tendsto (fun k : ℕ ↦ (2 : ℝ) ^ (-(k + 1 : ℝ))) atTop (𝓝 0) := by
    rw [← hrpowComp]
    exact (tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp harg
  -- Subtracting the vanishing power from the constant sequence gives the limit.
  have hleftTime :
      leftTime = fun k : ℕ ↦ 1 - (2 : ℝ) ^ (-(k + 1 : ℝ)) := by
    funext k
    exact leftTime_def k
  rw [hleftTime]
  simpa only [sub_zero] using tendsto_const_nhds.sub hpow

/-- The affine left template has Lipschitz constant given by the norm of its vector. -/
theorem lipschitzWith_leftTemplate {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (N₀ : E) :
    LipschitzWith ‖N₀‖₊ (leftTemplate N₀) := by
  -- Reduce Lipschitz continuity to the pointwise metric estimate.
  rw [lipschitzWith_iff_dist_le_mul]
  intro P Q
  rw [leftTemplate_apply, leftTemplate_apply]
  -- Factor the difference through scalar multiplication and use norm homogeneity.
  calc
    dist ((1 - P) • N₀) ((1 - Q) • N₀) =
        ‖((1 - P) - (1 - Q)) • N₀‖ := by
          rw [dist_eq_norm]
          congr 1
          rw [sub_smul]
          module
    _ ≤ ‖(1 - P) - (1 - Q)‖ * ‖N₀‖ := by exact norm_smul_le _ _
    _ = ‖N₀‖₊ * dist P Q := by
      rw [dist_eq_norm]
      simp only [Real.norm_eq_abs, coe_nnnorm]
      rw [abs_sub_comm]
      ring

/-- A vector of norm less than `1 / 32` determines a `1 / 32`-Lipschitz left template. -/
theorem lipschitzWith_leftTemplate_one_div_32 {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (N₀ : E) (hN₀ : ‖N₀‖ < (1 / 32 : ℝ)) :
    LipschitzWith (1 / 32 : NNReal) (leftTemplate N₀) := by
  -- Transfer the strict real norm bound to the ordered Lipschitz constants.
  have hconst : ‖N₀‖₊ ≤ (1 / 32 : NNReal) := by
    exact_mod_cast (le_of_lt hN₀)
  -- Weaken the exact constant supplied by the preceding theorem.
  exact (lipschitzWith_leftTemplate N₀).weaken hconst

end Lorentz
