/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Polar

/-!
# No polar point at ghost time

This module excludes polar points with positive coordinate equal to the ghost time.
-/

public section

namespace Lorentz

/- Lemma 7.5 (No polar point can occur at ghost time): a point of the Lorentz
subspace lying in the monotone polar of the ghost-curve operator graph cannot
have positive coordinate `1`. -/
#check (Lorentz.positiveCoordinate_ne_one_of_mem_ghostCurveOperator_polar :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (w : parametrizedSubspace d)
    (_ : w.val ∈ C0Seq.monotonePolar
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph),
    positiveCoordinate d hd w ≠ 1)

end Lorentz
