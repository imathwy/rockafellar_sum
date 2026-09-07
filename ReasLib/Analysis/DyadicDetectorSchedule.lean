module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ReasLib.Combinatorics.DetectorSchedule

public section

namespace DetectorTriple

/-- The integer-unit sign of a detector triple, viewed as a real scalar, is `-1` or `1`. -/
theorem coe_sign_eq_neg_one_or_one (t : DetectorTriple) :
    (t.sign : ℝ) = -1 ∨ (t.sign : ℝ) = 1 := by
  -- Split the integer sign classification, reverse its alternatives, and normalize each cast.
  rcases sign_eq_one_or_neg_one t with h | h
  · right
    norm_num [h]
  · left
    norm_num [h]

/-- The dyadic real sequence approaching `1` from above. -/
noncomputable def rightTime (i : ℕ) : ℝ :=
  1 + (2 : ℝ) ^ (-(i + 1 : ℝ))

/-- The defining formula for `rightTime`. -/
theorem rightTime_def (i : ℕ) :
    rightTime i = 1 + (2 : ℝ) ^ (-(i + 1 : ℝ)) := by
  -- Expose the defining dyadic expression without introducing any analytic side conditions.
  rfl

/-- The dyadic real radius sequence with exponent offset six. -/
noncomputable def rightRadius (i : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(i + 6 : ℝ))

/-- The defining formula for `rightRadius`. -/
theorem rightRadius_def (i : ℕ) :
    rightRadius i = (2 : ℝ) ^ (-(i + 6 : ℝ)) := by
  -- Expose the defining radius expression directly.
  rfl

/-- Half of the right-hand detector radius is positive. -/
theorem rightRadius_half_pos (i : ℕ) : 0 < rightRadius i / 2 := by
  -- Rewrite to the positive real-power formula, then preserve positivity through division by two.
  rw [rightRadius_def]
  positivity

/-- Adjacent right radii sum to `3 / 32` times the corresponding right-time gap. -/
theorem rightRadius_add_succ (i : ℕ) :
    rightRadius i + rightRadius (i + 1) =
      (3 / 32 : ℝ) * (rightTime i - rightTime (i + 1)) := by
  simp only [rightRadius_def, rightTime_def]
  have h_common : (2 : ℝ) ^ (-(i + 6 : ℝ)) =
      2 * (2 : ℝ) ^ (-(i + 7 : ℝ)) := by
    have h_exp : (-(i + 6 : ℝ)) = 1 + (-(i + 7 : ℝ)) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    rw [h_exp, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num [Real.rpow_one]
  have h_succ : (2 : ℝ) ^ (-((i + 1 : ℕ) + 6 : ℝ)) =
      (2 : ℝ) ^ (-(i + 7 : ℝ)) := by
    congr 1
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hdiff : (2 : ℝ) ^ (-(i + 1 : ℝ)) -
      (2 : ℝ) ^ (-((i + 1 : ℕ) + 1 : ℝ)) =
      (2 : ℝ) ^ (-(i + 2 : ℝ)) := by
    have h_factor : (2 : ℝ) ^ (-(i + 1 : ℝ)) =
        2 * (2 : ℝ) ^ (-(i + 2 : ℝ)) := by
      have h_exp : (-(i + 1 : ℝ)) = 1 + (-(i + 2 : ℝ)) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      rw [h_exp, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num [Real.rpow_one]
    have h_succ' : (2 : ℝ) ^ (-((i + 1 : ℕ) + 1 : ℝ)) =
        (2 : ℝ) ^ (-(i + 2 : ℝ)) := by
      congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    rw [h_factor, h_succ']
    ring
  rw [h_common, h_succ]
  rw [add_sub_add_left_eq_sub, hdiff]
  have h_rhs : (2 : ℝ) ^ (-(i + 2 : ℝ)) =
      32 * (2 : ℝ) ^ (-(i + 7 : ℝ)) := by
    have h_exp : (-(i + 2 : ℝ)) = 5 + (-(i + 7 : ℝ)) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    rw [h_exp, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num [Real.rpow_one]
  rw [h_rhs]
  ring

/-- Consecutive scheduled right times have the explicit zero-based dyadic gap. -/
theorem rightTime_sub_succ (i : ℕ) :
    rightTime i - rightTime (i + 1) = (2 : ℝ) ^ (-(i + 2 : ℝ)) := by
  simp only [rightTime_def]
  have h_factor : (2 : ℝ) ^ (-(i + 1 : ℝ)) =
      2 * (2 : ℝ) ^ (-(i + 2 : ℝ)) := by
    have h_exp : (-(i + 1 : ℝ)) = 1 + (-(i + 2 : ℝ)) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    rw [h_exp, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num [Real.rpow_one]
  have h_succ : (2 : ℝ) ^ (-((i + 1 : ℕ) + 1 : ℝ)) =
      (2 : ℝ) ^ (-(i + 2 : ℝ)) := by
    congr 1
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [add_sub_add_left_eq_sub, h_factor, h_succ]
  ring

/-- Consecutive scheduled right radii sum to `3 / 32` times the explicit
zero-based dyadic gap. -/
theorem rightRadius_add_succ_rpow (i : ℕ) :
    rightRadius i + rightRadius (i + 1) =
      (3 / 32 : ℝ) * (2 : ℝ) ^ (-(i + 2 : ℝ)) := by
  rw [rightRadius_add_succ, rightTime_sub_succ]

end DetectorTriple
