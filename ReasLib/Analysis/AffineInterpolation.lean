module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor

public section

universe u

/-- The affine line from `u` at time `a` to `v` at time `b` is `K`-Lipschitz
on `Set.Icc a b` when the distance between its endpoints is at most
`K * (b - a)`. -/
theorem AffineMap.lipschitzOnWith_lineMap_interval
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {u v : E} {K : NNReal} (hab : a < b)
    (huv : ‖v - u‖ ≤ (K : ℝ) * (b - a)) :
    LipschitzOnWith K
      (fun t : ℝ ↦ AffineMap.lineMap u v ((t - a) / (b - a))) (Set.Icc a b) := by
  -- The endpoint hypothesis bounds the constant metric slope of the segment.
  have hba : 0 < b - a := sub_pos.mpr hab
  have hslope : dist u v / (b - a) ≤ (K : ℝ) := by
    rw [div_le_iff₀ hba, dist_eq_norm, norm_sub_rev]
    exact huv
  -- Prove the stronger global estimate, then restrict it to the given interval.
  refine (LipschitzWith.of_dist_le_mul fun x y ↦ ?_).lipschitzOnWith
  have hparam :
      dist ((x - a) / (b - a)) ((y - a) / (b - a)) = dist x y / (b - a) := by
    rw [Real.dist_eq, Real.dist_eq, div_sub_div_same, sub_sub_sub_cancel_right,
      abs_div, abs_of_pos hba]
  calc
    dist (AffineMap.lineMap u v ((x - a) / (b - a)))
          (AffineMap.lineMap u v ((y - a) / (b - a))) =
        dist x y / (b - a) * dist u v := by
          rw [dist_lineMap_lineMap, hparam]
    _ = (dist u v / (b - a)) * dist x y := by ring
    _ ≤ (K : ℝ) * dist x y := mul_le_mul_of_nonneg_right hslope dist_nonneg

/-- The affine line from `u` to `v`, reparameterized over `Set.Icc a b`, maps
into every convex set containing both endpoints. -/
theorem Convex.mapsTo_lineMap_interval
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {u v : E} {C : Set E} (hab : a < b)
    (hC : Convex ℝ C) (hu : u ∈ C) (hv : v ∈ C) :
    Set.MapsTo
      (fun t : ℝ ↦ AffineMap.lineMap u v ((t - a) / (b - a))) (Set.Icc a b) C := by
  -- Normalization sends every time in `[a, b]` to a line-map parameter in `[0, 1]`.
  intro t ht
  have hba : 0 < b - a := sub_pos.mpr hab
  have hparam : (t - a) / (b - a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hba.le
    · exact (div_le_one hba).mpr (sub_le_sub_right ht.2 a)
  -- Convexity retains the entire line segment between the two endpoints.
  exact hC.lineMap_mem hu hv hparam
