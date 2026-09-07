/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteTimeZero

/-!
# A negative-energy time-zero point

This module constructs a remote-ball point with zero positive coordinate and negative energy.
-/

public section

/- Lemma 6.2 (A negative-energy time-zero point away from $U$) (1): a point at
positive Lorentz coordinate zero whose first coordinate lies in the remote ball
and whose negative coordinate approximates the prescribed target. -/
#check (Lorentz.exists_remoteTimeZero :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (nbar : HilbertProd2 UnitL2) (hnbar : ‖nbar‖ = (1 / 64 : ℝ)),
    ∃ z₀ : Lorentz.parametrizedSubspace d,
      Lorentz.positiveCoordinate d hd z₀ = 0 ∧
      (z₀ : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖Lorentz.negativeCoordinate d hd z₀ - nbar‖ < (1 / 128 : ℝ))

/- Lemma 6.2 (A negative-energy time-zero point away from $U$) (2): the norm
of a negative coordinate approximating the prescribed target lies strictly
between zero and `1 / 32`. -/
#check (Lorentz.negativeCoordinate_norm_mem_Ioo :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (nbar : HilbertProd2 UnitL2) (hnbar : ‖nbar‖ = (1 / 64 : ℝ))
    (z₀ : Lorentz.parametrizedSubspace d)
    (happrox : ‖Lorentz.negativeCoordinate d hd z₀ - nbar‖ < (1 / 128 : ℝ)),
    ‖Lorentz.negativeCoordinate d hd z₀‖ ∈ Set.Ioo 0 (1 / 32 : ℝ))

/- Lemma 6.2 (A negative-energy time-zero point away from $U$) (3): at
positive Lorentz coordinate zero, the quadratic pairing is the negative square
of the negative-coordinate norm. -/
#check (Lorentz.quadraticPairing_eq_neg_sq_of_timeZero :
  ∀ (d : C0Seq) (hd : d ≠ 0) (z₀ : Lorentz.parametrizedSubspace d)
    (hP : Lorentz.positiveCoordinate d hd z₀ = 0),
    C0Seq.quadraticPairing z₀ = -‖Lorentz.negativeCoordinate d hd z₀‖ ^ 2)

/- Lemma 6.2 (A negative-energy time-zero point away from $U$) (4): a
time-zero point whose negative coordinate approximates the prescribed nonzero
target has strictly negative quadratic energy. -/
#check (Lorentz.quadraticPairing_neg_of_timeZero_approx :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (nbar : HilbertProd2 UnitL2) (hnbar : ‖nbar‖ = (1 / 64 : ℝ))
    (z₀ : Lorentz.parametrizedSubspace d)
    (hP : Lorentz.positiveCoordinate d hd z₀ = 0)
    (happrox : ‖Lorentz.negativeCoordinate d hd z₀ - nbar‖ < (1 / 128 : ℝ)),
    C0Seq.quadraticPairing z₀ < 0)
