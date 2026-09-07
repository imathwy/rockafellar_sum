/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates

/-!
# Folded right-vertex Lipschitz bounds

This module bounds displacement of adjacent folded right vertices by their
scheduled radii and time gaps.
-/

public section

namespace Lorentz

/-- The negative-coordinate displacement of adjacent folded right vertices is
strictly smaller than the sum of their scheduled radii. -/
theorem norm_negativeCoordinate_rightVertex_sub_lt (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) -
        negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1))‖ <
      DetectorTriple.rightRadius i + DetectorTriple.rightRadius (i + 1) := by
  have hi := norm_negativeCoordinate_rightVertex_lt d hd h_missing h h_tendsto i
  have hi1 := norm_negativeCoordinate_rightVertex_lt d hd h_missing h h_tendsto (i + 1)
  calc
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) -
        negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1))‖ ≤
        ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i)‖ +
          ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1))‖ :=
      norm_sub_le _ _
    _ < DetectorTriple.rightRadius i + DetectorTriple.rightRadius (i + 1) :=
      add_lt_add hi hi1

/-- The negative-coordinate displacement of adjacent folded right vertices is
strictly smaller than their scheduled right-time gap. -/
theorem rightVertex_slope_lt_one (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) -
        negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1))‖ <
      DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1) := by
  have hnorm := norm_negativeCoordinate_rightVertex_sub_lt
    d hd h_missing h h_tendsto i
  have hrad := DetectorTriple.rightRadius_add_succ i
  have hgap : 0 < DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1) := by
    rw [DetectorTriple.rightTime_sub_succ]
    positivity
  calc
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) -
        negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1))‖ <
        DetectorTriple.rightRadius i + DetectorTriple.rightRadius (i + 1) := hnorm
    _ = (3 / 32 : ℝ) * (DetectorTriple.rightTime i -
        DetectorTriple.rightTime (i + 1)) := hrad
    _ < DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1) := by
      nlinarith

end Lorentz
