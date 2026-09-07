/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftAnchor
public import S2.GhostCurve.Lemma_6_2_A_negative_energy_time_zero_point_away_from_U

/-!
# Quantitative Left Anchor

This module exposes the quantitative left-anchor existence result.
-/

public section

/- Lemma 6.3a (Quantitative left-anchor choice): given a point `z₀` with
sufficiently small negative coordinate, there is a point at positive coordinate
`-1` whose first coordinate lies in `C0Seq.remoteBall`, whose negative coordinate
approximates twice that of `z₀`, and which satisfies the resulting norm bounds. -/
#check (Lorentz.exists_leftAnchor :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ) →
    ∃ zLeft : Lorentz.parametrizedSubspace d,
      Lorentz.positiveCoordinate d hd zLeft = -1 ∧
      (zLeft : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖Lorentz.negativeCoordinate d hd zLeft -
          (2 : ℝ) • Lorentz.negativeCoordinate d hd z₀‖ < (1 / 64 : ℝ) ∧
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 / 16 : ℝ) ∧
      ‖Lorentz.negativeCoordinate d hd zLeft -
          Lorentz.negativeCoordinate d hd z₀‖ < 1)
