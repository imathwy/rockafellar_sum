/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates
public import ReasLib.Analysis.AffineInterpolation

/-!
# Folded-to-future affine interpolation

This module bounds the final affine bridge from a folded right vertex to the
future-ray base point.
-/

public section

namespace Lorentz

/-- The negative-coordinate gap from the first folded right vertex to
`(2 : ℝ) • v` is strictly less than `1 / 2`. -/
theorem foldedToFuture_gap_lt_half (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16) :
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) -
        negativeCoordinate d hd ((2 : ℝ) • v)‖ < (1 : ℝ) / 2 := by
  have hrv := norm_negativeCoordinate_rightVertex_lt d hd h_missing h h_tendsto 0
  have hv2 : ‖negativeCoordinate d hd ((2 : ℝ) • v)‖ =
      2 * ‖negativeCoordinate d hd v‖ := by
    rw [map_smul, norm_smul]
    norm_num
  have hrv0 : DetectorTriple.rightRadius 0 < (1 : ℝ) / 8 := by
    rw [DetectorTriple.rightRadius_def]
    norm_num
  calc
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) -
        negativeCoordinate d hd ((2 : ℝ) • v)‖ ≤
        ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0)‖ +
          ‖negativeCoordinate d hd ((2 : ℝ) • v)‖ := norm_sub_le _ _
    _ < DetectorTriple.rightRadius 0 + 2 * ‖negativeCoordinate d hd v‖ := by
      rw [hv2]
      exact add_lt_add_of_lt_of_le hrv (le_rfl)
    _ < (1 : ℝ) / 2 := by
      nlinarith

/-- The negative-coordinate affine edge from the first folded right vertex at
`3 / 2` to `(2 : ℝ) • v` at `2` has a Lipschitz constant strictly less than `1`. -/
theorem foldedToFutureEdge_slope_lt_one (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16) :
    ∃ K : NNReal, K < 1 ∧
      LipschitzOnWith K
        (fun P : ℝ ↦
          AffineMap.lineMap
            (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0))
            (negativeCoordinate d hd ((2 : ℝ) • v))
            ((P - (3 / 2 : ℝ)) / (2 - 3 / 2)))
        (Set.Icc (3 / 2 : ℝ) 2) := by
  have hgap := foldedToFuture_gap_lt_half d hd h_missing h h_tendsto v hvN
  let K : NNReal := ⟨2 * ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) -
      negativeCoordinate d hd ((2 : ℝ) • v)‖, by positivity⟩
  have hK : (K : ℝ) < 1 := by
    change 2 * ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) -
      negativeCoordinate d hd ((2 : ℝ) • v)‖ < 1
    nlinarith [hgap]
  refine ⟨K, hK, ?_⟩
  apply AffineMap.lipschitzOnWith_lineMap_interval
  · norm_num
  · change ‖negativeCoordinate d hd ((2 : ℝ) • v) -
      negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0)‖ ≤
      (K : ℝ) * (2 - (3 / 2 : ℝ))
    rw [show 2 - (3 / 2 : ℝ) = (1 : ℝ) / 2 by norm_num]
    change ‖negativeCoordinate d hd ((2 : ℝ) • v) -
      negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0)‖ ≤
      (2 * ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) -
        negativeCoordinate d hd ((2 : ℝ) • v)‖) * (1 / 2 : ℝ)
    rw [norm_sub_rev]
    nlinarith [norm_nonneg
      (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) -
        negativeCoordinate d hd ((2 : ℝ) • v))]

end Lorentz
