/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.Localization

/-!
# Local nonnegative pairing

This module records nonnegative quadratic pairing on the ghost graph over the local ball.
-/

public section

namespace Lorentz

/- Lemma 7.8 (Local nonnegative pairing on the unit ball) (1): the quadratic
pairing of `(x, xstar)` is the dual pairing of `x` and `xstar`. -/
#check (C0Seq.quadraticPairing_apply :
  ∀ (x : C0Seq) (xstar : L1Seq),
    C0Seq.quadraticPairing (x, xstar) = C0Seq.pairingL x xstar)

/- Lemma 7.8 (Local nonnegative pairing on the unit ball) (2): a point in the
graph of the ghost-curve operator whose primal component lies in
`C0Seq.localOpenUnitBall` has nonnegative quadratic pairing. -/
#check (Lorentz.quadraticPairing_nonneg_of_mem_ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (hNZero : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (x : C0Seq) (xstar : L1Seq),
    (x, xstar) ∈ (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph →
      x ∈ C0Seq.localOpenUnitBall →
        0 ≤ C0Seq.quadraticPairing (x, xstar))

end Lorentz
