module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding

#check (Lorentz.embedding : ∀ (d : C0Seq), d ≠ 0 →
  Lorentz.parametrizedSubspace d →ₗ[ℝ] ℝ × HilbertProd2 UnitL2)

/- Definition 4.5 (The Lorentz embedding and its image) (1): `Λ z` is the
pair `(P z, N z)` of Lorentz coordinates. -/
#check (Lorentz.embedding_apply : ∀ (d : C0Seq) (hd : d ≠ 0)
  (z : Lorentz.parametrizedSubspace d),
  Lorentz.embedding d hd z =
    (Lorentz.positiveCoordinate d hd z, Lorentz.negativeCoordinate d hd z))

#check (Lorentz.embeddingRange : ∀ (d : C0Seq), d ≠ 0 →
  Submodule ℝ (ℝ × HilbertProd2 UnitL2))

/- Definition 4.5 (The Lorentz embedding and its image) (2): `E` is the image
of `Λ`, so its points are exactly the values `Λ z`. -/
#check (Lorentz.mem_embeddingRange : ∀ (d : C0Seq) (hd : d ≠ 0)
  (y : ℝ × HilbertProd2 UnitL2),
  y ∈ Lorentz.embeddingRange d hd ↔
    ∃ z : Lorentz.parametrizedSubspace d, Lorentz.embedding d hd z = y)
