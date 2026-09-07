module

public import Mathlib.Analysis.Normed.Group.Uniform

universe u

namespace LipschitzWith

/-- Two vectors with radial norm bounds on opposite sides of an anchor satisfy the
corresponding Lipschitz estimate. -/
private lemma dist_le_mul_of_norm_le_of_le_anchor {E : Type u} [SeminormedAddGroup E]
    {K : NNReal} {a x y : ℝ} {u v : E} (hxa : x ≤ a) (hay : a ≤ y)
    (hu : ‖u‖ ≤ K * |x - a|) (hv : ‖v‖ ≤ K * |y - a|) :
    dist u v ≤ K * dist x y := by
  -- First replace the distance by the sum of the two radial bounds.
  calc
    dist u v ≤ ‖u‖ + ‖v‖ := dist_le_norm_add_norm u v
    _ ≤ K * |x - a| + K * |y - a| := add_le_add hu hv
    -- The anchor lies between the points, so the two radial lengths add to `dist x y`.
    _ = K * dist x y := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxa),
        abs_of_nonneg (sub_nonneg.mpr hay),
        abs_of_nonpos (sub_nonpos.mpr (hxa.trans hay))]
      ring

/-- A map from the real line into a seminormed additive group is globally Lipschitz
when it vanishes at an anchor, is Lipschitz on both closed half-lines at that anchor,
and its norm is bounded by the Lipschitz constant times the distance to the anchor. -/
public theorem of_iic_ici_of_norm_le (a : ℝ) {E : Type u} [SeminormedAddGroup E]
    {K : NNReal} {f : ℝ → E} (_ : f a = 0)
    (h_left : LipschitzOnWith K f (Set.Iic a))
    (h_right : LipschitzOnWith K f (Set.Ici a))
    (h_bound : ∀ P : ℝ, ‖f P‖ ≤ K * |P - a|) : LipschitzWith K f := by
  -- It suffices to establish the metric inequality for an arbitrary pair of points.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  by_cases hxa : x ≤ a
  · by_cases hya : y ≤ a
    · -- Points on the left are controlled by the left-hand Lipschitz hypothesis.
      exact h_left.dist_le_mul x hxa y hya
    · -- For a pair crossing the anchor, use the two radial norm estimates.
      exact dist_le_mul_of_norm_le_of_le_anchor hxa (le_of_not_ge hya)
        (h_bound x) (h_bound y)
  · by_cases hay : a ≤ y
    · -- Points on the right are controlled by the right-hand Lipschitz hypothesis.
      exact h_right.dist_le_mul x (le_of_not_ge hxa) y hay
    · -- Reverse a crossing pair to put its left endpoint first.
      rw [dist_comm (f x) (f y), dist_comm x y]
      exact dist_le_mul_of_norm_le_of_le_anchor (le_of_not_ge hay) (le_of_not_ge hxa)
        (h_bound y) (h_bound x)

end LipschitzWith
