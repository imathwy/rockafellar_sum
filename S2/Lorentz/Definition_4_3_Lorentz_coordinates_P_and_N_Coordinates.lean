/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates

/-!
# Lorentz Coordinate API

This module exposes coordinate maps and their parametrized-point formulas.
-/

#check (Lorentz.parametrizedPoint :
  (d : C0Seq) → L1Seq → ℝ → Lorentz.parametrizedSubspace d)

#check (Lorentz.parametrizedPoint_apply :
  ∀ (d : C0Seq) (a : L1Seq) (t : ℝ),
    (Lorentz.parametrizedPoint d a t : C0Seq × L1Seq) =
      Lorentz.parametrization d (a, t))

#check (Lorentz.positiveCoordinate :
  ∀ (d : C0Seq), d ≠ 0 → Lorentz.parametrizedSubspace d →ₗ[ℝ] ℝ)

#check (Lorentz.positiveCoordinate_apply :
  ∀ (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ),
    Lorentz.positiveCoordinate d hd (Lorentz.parametrizedPoint d a t) =
      (t + C0Seq.pairingL d a) / 2)

#check (Lorentz.negativeCoordinate :
  ∀ (d : C0Seq),
    d ≠ 0 → Lorentz.parametrizedSubspace d →ₗ[ℝ] HilbertProd2 UnitL2)

#check (Lorentz.negativeCoordinate_apply :
  ∀ (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ),
    Lorentz.negativeCoordinate d hd (Lorentz.parametrizedPoint d a t) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        ((t - C0Seq.pairingL d a) / 2))
