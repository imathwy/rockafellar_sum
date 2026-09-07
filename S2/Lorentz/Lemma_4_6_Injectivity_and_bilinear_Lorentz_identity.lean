module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.Injective
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

public section

open scoped InnerProductSpace

/-
Lemma 4.6 (Injectivity and bilinear Lorentz identity) (1). The map
`Lorentz.embedding d hd` is a real-linear map.
-/
#check (Lorentz.embedding : ∀ (d : C0Seq), d ≠ 0 →
  Lorentz.parametrizedSubspace d →ₗ[ℝ] ℝ × HilbertProd2 UnitL2)

/-
Lemma 4.6 (Injectivity and bilinear Lorentz identity) (2). The Lorentz
embedding is injective.
-/
#check (Lorentz.embedding_injective : ∀ (d : C0Seq) (hd : d ≠ 0),
  Function.Injective (Lorentz.embedding d hd))

/-
Lemma 4.6 (Injectivity and bilinear Lorentz identity) (3). The symmetric form
is twice the Lorentz inner-product expression in positive and negative coordinates.
-/
#check (Lorentz.symmetricForm_eq_coordinates :
  ∀ (d : C0Seq) (hd : d ≠ 0) (z w : Lorentz.parametrizedSubspace d),
    C0Seq.symmetricForm z w =
      2 * (Lorentz.positiveCoordinate d hd z * Lorentz.positiveCoordinate d hd w -
        ⟪Lorentz.negativeCoordinate d hd z, Lorentz.negativeCoordinate d hd w⟫_ℝ))
