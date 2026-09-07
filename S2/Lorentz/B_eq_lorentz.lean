/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Lorentz polarization identity

This source-facing module records the symmetric-form expression in Lorentz
coordinates.
-/

@[expose] public section

open scoped InnerProductSpace

/-
Lemma 4.6b (Polarization of the Lorentz quadratic identity): on
`Lorentz.parametrizedSubspace d`, the symmetric form is twice the Lorentz scalar product.
-/
#check (Lorentz.symmetricForm_eq_coordinates :
  ∀ (d : C0Seq) (hd : d ≠ 0) (z w : Lorentz.parametrizedSubspace d),
    C0Seq.symmetricForm z w =
      2 * (Lorentz.positiveCoordinate d hd z * Lorentz.positiveCoordinate d hd w -
        ⟪Lorentz.negativeCoordinate d hd z, Lorentz.negativeCoordinate d hd w⟫_ℝ))
