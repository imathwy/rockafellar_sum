/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Bilinear-form polarization

This module records the diagonal criterion for equality of continuous real
bilinear symmetric parts.
-/

universe u

namespace ContinuousLinearMap

/-- Continuous real bilinear forms with equal diagonal values have equal symmetric parts. -/
public theorem add_flip_eq_add_flip_of_diagonal_eq {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B C : E →L[ℝ] E →L[ℝ] ℝ) (hdiag : ∀ x, B x x = C x x) :
    B + B.flip = C + C.flip := by
  -- Reduce equality of the symmetric parts to equality on two arbitrary vectors.
  ext x y
  -- Expanding the diagonal identity at `x + y` exposes both mixed terms.
  have hsum := hdiag (x + y)
  have hx := hdiag x
  have hy := hdiag y
  simp only [map_add, add_apply] at hsum
  -- Cancel the equal diagonal terms in the real polarization identity.
  simp only [add_apply, flip_apply]
  linarith

end ContinuousLinearMap
