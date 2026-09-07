/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.RemoteBall
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive

/-!
# Left Anchor

This module constructs a normalized left anchor with quantitative negative-coordinate bounds.
-/

public section

namespace Lorentz

/-- A point with sufficiently small negative coordinate admits a negative-one
anchor in the remote ball whose negative coordinate approximates twice the
original one and satisfies the resulting quantitative norm bounds. -/
theorem exists_leftAnchor (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) :
    ∃ zLeft : parametrizedSubspace d,
      positiveCoordinate d hd zLeft = -1 ∧
      (zLeft : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖negativeCoordinate d hd zLeft -
          (2 : ℝ) • negativeCoordinate d hd z₀‖ < (1 / 64 : ℝ) ∧
      ‖negativeCoordinate d hd zLeft‖ < (1 / 16 : ℝ) ∧
      ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1 := by
  -- Choose a tolerance that fits both the advertised approximation and the
  -- remaining norm budget after accounting for twice the original coordinate.
  let ε : ℝ := min (1 / 64) (1 / 16 - 2 * ‖negativeCoordinate d hd z₀‖)
  have hGap : 0 < (1 / 16 : ℝ) - 2 * ‖negativeCoordinate d hd z₀‖ := by
    nlinarith
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (by norm_num) hGap
  have hε_le_radius : ε ≤ (1 / 64 : ℝ) := by
    exact min_le_left _ _
  have hε_le_budget : ε ≤ (1 / 16 : ℝ) -
      2 * ‖negativeCoordinate d hd z₀‖ := by
    exact min_le_right _ _
  -- Apply simultaneous approximation at positive coordinate `-1` with the
  -- negative target reconstructed from its two Hilbert-product components.
  obtain ⟨zLeft, hPositive, hAmbient, hNegative⟩ :=
    exists_approx_fixedPositiveCoordinate d hd h_missing (-1) C0Seq.farPoint
      (HilbertProd2.fst ((2 : ℝ) • negativeCoordinate d hd z₀))
      (HilbertProd2.snd ((2 : ℝ) • negativeCoordinate d hd z₀)) ε hε
  have hTarget : HilbertProd2.mk
      (HilbertProd2.fst ((2 : ℝ) • negativeCoordinate d hd z₀))
      (HilbertProd2.snd ((2 : ℝ) • negativeCoordinate d hd z₀)) =
        (2 : ℝ) • negativeCoordinate d hd z₀ := by
    exact HilbertProd2.mk_fst_snd _
  rw [hTarget] at hNegative
  have hRemote : (zLeft : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall := by
    rw [C0Seq.mem_remoteBall]
    have hε_lt_one : ε < 1 := lt_of_le_of_lt hε_le_radius (by norm_num)
    simpa only [dist_eq_norm] using lt_trans hAmbient hε_lt_one
  have hApprox : ‖negativeCoordinate d hd zLeft -
      (2 : ℝ) • negativeCoordinate d hd z₀‖ < (1 / 64 : ℝ) :=
    lt_of_lt_of_le hNegative hε_le_radius
  -- The adaptive budget and the triangle inequality give the sharper norm bound.
  have hNormTriangle : ‖negativeCoordinate d hd zLeft‖ ≤
      ‖negativeCoordinate d hd zLeft -
        (2 : ℝ) • negativeCoordinate d hd z₀‖ +
      ‖(2 : ℝ) • negativeCoordinate d hd z₀‖ := by
    calc
      ‖negativeCoordinate d hd zLeft‖ =
          ‖(negativeCoordinate d hd zLeft -
            (2 : ℝ) • negativeCoordinate d hd z₀) +
            (2 : ℝ) • negativeCoordinate d hd z₀‖ := by
              rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hScaledNorm : ‖(2 : ℝ) • negativeCoordinate d hd z₀‖ =
      2 * ‖negativeCoordinate d hd z₀‖ := by
    rw [norm_smul]
    norm_num
  rw [hScaledNorm] at hNormTriangle
  have hNorm : ‖negativeCoordinate d hd zLeft‖ < (1 / 16 : ℝ) := by
    nlinarith
  -- A second triangle inequality makes the anchor difference far smaller than one.
  have hDifferenceTriangle :
      ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ ≤
        ‖negativeCoordinate d hd zLeft‖ + ‖negativeCoordinate d hd z₀‖ :=
    norm_sub_le _ _
  have hDifference :
      ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1 := by
    nlinarith
  exact ⟨zLeft, hPositive, hRemote, hApprox, hNorm, hDifference⟩

end Lorentz
