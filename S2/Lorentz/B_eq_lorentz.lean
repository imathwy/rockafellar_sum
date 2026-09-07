module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

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
