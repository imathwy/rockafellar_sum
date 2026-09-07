/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Lorentz cones

This module defines the future and past Lorentz cones and their basic norm
and convexity API.
-/

@[expose] public section

universe u

namespace Lorentz

/-- The future Lorentz cone on a real normed coordinate space. -/
def futureCone (H0 : Type u) [Norm H0] : Set (ℝ × H0) :=
  {x | ‖x.2‖ ≤ x.1}

/-- Membership in the future Lorentz cone is the inequality `‖N‖ ≤ P`. -/
@[simp]
theorem mem_futureCone {H0 : Type u} [Norm H0] (x : ℝ × H0) :
    x ∈ futureCone H0 ↔ ‖x.2‖ ≤ x.1 := by
  -- Unfold the cone to expose its defining coordinate inequality.
  rfl

/-- The past Lorentz cone on a real normed coordinate space. -/
def pastCone (H0 : Type u) [Norm H0] : Set (ℝ × H0) :=
  {x | ‖x.2‖ ≤ -x.1}

/-- Membership in the past Lorentz cone is the inequality `‖N‖ ≤ -P`. -/
@[simp]
theorem mem_pastCone {H0 : Type u} [Norm H0] (x : ℝ × H0) :
    x ∈ pastCone H0 ↔ ‖x.2‖ ≤ -x.1 := by
  -- Unfold the cone to expose its defining coordinate inequality.
  rfl

/-- The Lorentz energy `P ^ 2 - ‖N‖ ^ 2` of a point `(P, N)`. -/
def energy {H0 : Type u} [Norm H0] (x : ℝ × H0) : ℝ :=
  x.1 ^ 2 - ‖x.2‖ ^ 2

/-- The Lorentz energy in product coordinates. -/
theorem energy_apply {H0 : Type u} [Norm H0] (P : ℝ) (N : H0) :
    energy (P, N) = P ^ 2 - ‖N‖ ^ 2 := by
  -- Product projections reduce the energy to its coordinate formula.
  rfl

/-- A point in the future Lorentz cone has nonnegative Lorentz energy. -/
theorem energy_nonneg_of_mem_futureCone {H0 : Type u} [SeminormedAddCommGroup H0]
    {x : ℝ × H0} (hx : x ∈ futureCone H0) : 0 ≤ energy x := by
  -- Cone membership places both sides of the norm bound in the nonnegative half-line.
  have hbound : ‖x.2‖ ≤ x.1 := (mem_futureCone x).mp hx
  have hfirst : 0 ≤ x.1 := (norm_nonneg x.2).trans hbound
  -- Squaring preserves the bound, which is exactly nonnegativity of the energy.
  rw [energy]
  exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg x.2) hfirst).mpr hbound)

/-- A point in the past Lorentz cone has nonnegative Lorentz energy. -/
theorem energy_nonneg_of_mem_pastCone {H0 : Type u} [SeminormedAddCommGroup H0]
    {x : ℝ × H0} (hx : x ∈ pastCone H0) : 0 ≤ energy x := by
  -- Cone membership bounds the norm by the nonnegative quantity `-x.1`.
  have hbound : ‖x.2‖ ≤ -x.1 := (mem_pastCone x).mp hx
  have hnegFirst : 0 ≤ -x.1 := (norm_nonneg x.2).trans hbound
  have hsquare : ‖x.2‖ ^ 2 ≤ (-x.1) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg x.2) hnegFirst).mpr hbound
  -- The square removes the sign, leaving the energy difference nonnegative.
  rw [energy]
  exact sub_nonneg.mpr (by simpa only [neg_sq] using hsquare)

/-- The future Lorentz cone is convex. -/
theorem convex_futureCone (H0 : Type u) [SeminormedAddCommGroup H0] [NormedSpace ℝ H0] :
    Convex ℝ (futureCone H0) := by
  -- It suffices to control an arbitrary convex combination of two cone points.
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rw [mem_futureCone] at hx hy ⊢
  -- Convexity of the norm supplies the geometric bound; endpoint inequalities finish it.
  calc
    ‖(a • x + b • y).2‖ ≤ a * ‖x.2‖ + b * ‖y.2‖ := by
      simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using
        (convexOn_univ_norm.2 (Set.mem_univ x.2) (Set.mem_univ y.2) ha hb hab)
    _ ≤ a * x.1 + b * y.1 :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = (a • x + b • y).1 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]

/-- The past Lorentz cone is convex. -/
theorem convex_pastCone (H0 : Type u) [SeminormedAddCommGroup H0] [NormedSpace ℝ H0] :
    Convex ℝ (pastCone H0) := by
  -- It suffices to control an arbitrary convex combination of two cone points.
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rw [mem_pastCone] at hx hy ⊢
  -- Apply the same norm estimate, then collect the two negated first coordinates.
  calc
    ‖(a • x + b • y).2‖ ≤ a * ‖x.2‖ + b * ‖y.2‖ := by
      simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using
        (convexOn_univ_norm.2 (Set.mem_univ x.2) (Set.mem_univ y.2) ha hb hab)
    _ ≤ a * (-x.1) + b * (-y.1) :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = -(a * x.1 + b * y.1) := by
      ring
    _ = -(a • x + b • y).1 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]

/-- Affine interpolation between points of the future cone has nonnegative Lorentz energy. -/
theorem energy_lineMap_nonneg_of_mem_futureCone
    {H0 : Type u} [SeminormedAddCommGroup H0] [NormedSpace ℝ H0]
    {x y : ℝ × H0} (hx : x ∈ futureCone H0) (hy : y ∈ futureCone H0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ energy (AffineMap.lineMap x y t) := by
  -- Convexity keeps the affine interpolation inside the future cone.
  have hline : AffineMap.lineMap x y t ∈ futureCone H0 :=
    (convex_futureCone H0).lineMap_mem hx hy ht
  -- Cone membership supplies the established energy invariant.
  exact energy_nonneg_of_mem_futureCone hline

/-- Affine interpolation between points of the past cone has nonnegative Lorentz energy. -/
theorem energy_lineMap_nonneg_of_mem_pastCone
    {H0 : Type u} [SeminormedAddCommGroup H0] [NormedSpace ℝ H0]
    {x y : ℝ × H0} (hx : x ∈ pastCone H0) (hy : y ∈ pastCone H0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ energy (AffineMap.lineMap x y t) := by
  -- Convexity keeps the affine interpolation inside the past cone.
  have hline : AffineMap.lineMap x y t ∈ pastCone H0 :=
    (convex_pastCone H0).lineMap_mem hx hy ht
  -- Cone membership supplies the established energy invariant.
  exact energy_nonneg_of_mem_pastCone hline

end Lorentz
