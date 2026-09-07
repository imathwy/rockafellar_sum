/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Lipschitz

/-!
# Cross-ghost Lipschitz bounds

This module records the cross-ghost estimate completing global Lipschitz control.
-/

public section

namespace Lorentz

/- Lemma 6.20b (Cross-ghost Lipschitz bound) (1): parameters on opposite sides
of the ghost time satisfy the two-step norm estimate through the zero anchor. -/
#check (Lorentz.ghostCurveN_crossBounds :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P Q : ℝ) (_ : P < 1) (_ : 1 < Q),
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v Q -
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤
      ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v Q‖ +
        ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ∧
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v Q‖ +
        ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤ Q - P)

/- Lemma 6.20b (Cross-ghost Lipschitz bound) (2): the two same-side estimates
and the cross-ghost bound make the negative-coordinate curve globally
`1`-Lipschitz. -/
#check (Lorentz.lipschitzWith_ghostCurveN :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    LipschitzWith 1 (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v))

end Lorentz
