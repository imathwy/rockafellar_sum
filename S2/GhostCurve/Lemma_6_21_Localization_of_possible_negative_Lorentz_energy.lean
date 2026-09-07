/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Localization

/-!
# Localization of negative Lorentz energy

This module localizes negative-energy curve points to the remote ball.
-/

public section

namespace Lorentz

/- Lemma 6.21 (Localization of possible negative Lorentz energy) (1): a point
on the assembled curve with negative quadratic pairing has primal component in
`C0Seq.remoteBall`. -/
#check (Lorentz.ghostCurveN_primal_mem_remoteBall_of_quadraticPairing_neg :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd zLeft = -1)
    (_ : Lorentz.positiveCoordinate d hd z₀ = 0)
    (_ : ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (_ : zLeft.1.1 ∈ C0Seq.remoteBall)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd v = 1)
    (_ : ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (z : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.negativeCoordinate d hd z =
      Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (Lorentz.positiveCoordinate d hd z))
    (_ : C0Seq.quadraticPairing z < 0),
    z.1.1 ∈ C0Seq.remoteBall)

/- Lemma 6.21 (Localization of possible negative Lorentz energy) (2): a point
on the assembled curve whose primal component lies in `C0Seq.localOpenUnitBall`
has nonnegative quadratic pairing. -/
#check (Lorentz.ghostCurveN_quadraticPairing_nonneg_of_primal_mem_localBall :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd zLeft = -1)
    (_ : Lorentz.positiveCoordinate d hd z₀ = 0)
    (_ : ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (_ : zLeft.1.1 ∈ C0Seq.remoteBall)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd v = 1)
    (_ : ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (z : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.negativeCoordinate d hd z =
      Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (Lorentz.positiveCoordinate d hd z))
    (_ : z.1.1 ∈ C0Seq.localOpenUnitBall),
    0 ≤ C0Seq.quadraticPairing z)

end Lorentz
