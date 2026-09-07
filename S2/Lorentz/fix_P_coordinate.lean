/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive

/-!
# Fixing the positive Lorentz coordinate

This module exposes the adjusted scalar parameter and its positive and negative
coordinate formulas.
-/

public section

namespace Lorentz

/- The adjusted parameter prescribes the positive Lorentz coordinate exactly. -/
#check (Lorentz.positiveCoordinate_adjustedParameter :
  ∀ (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (p : ℝ),
    positiveCoordinate d hd
      (parametrizedPoint d a (2 * p - C0Seq.pairingL d a)) = p)

/- The adjusted parameter gives the stated negative Lorentz coordinate. -/
#check (Lorentz.negativeCoordinate_adjustedParameter :
  ∀ (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (p : ℝ),
    negativeCoordinate d hd
      (parametrizedPoint d a (2 * p - C0Seq.pairingL d a)) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        (p - C0Seq.pairingL d a))

/- The adjusted parametrized point has the stated first ambient coordinate. -/
#check (Lorentz.parametrizedPoint_fst_adjustedParameter :
  ∀ (d : C0Seq) (a : L1Seq) (p : ℝ),
    (parametrizedPoint d a (2 * p - C0Seq.pairingL d a) :
        C0Seq × L1Seq).1 =
      -L1Seq.positiveOperator a + (2 * p - C0Seq.pairingL d a) • d)

/- Lemma 4.10b (Exact enforcement of the P coordinate) -/
#check (Lorentz.exists_approx_fixedPositiveCoordinate :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (_ : d ∉ Set.range L1Seq.positiveOperator)
    (p : ℝ) (x₀ : C0Seq) (v : UnitL2) (r ε : ℝ) (_ : 0 < ε),
    ∃ z : parametrizedSubspace d,
      positiveCoordinate d hd z = p ∧
      ‖(z : C0Seq × L1Seq).1 - x₀‖ < ε ∧
      ‖negativeCoordinate d hd z - HilbertProd2.mk v r‖ < ε)

end Lorentz
