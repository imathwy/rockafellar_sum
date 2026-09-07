module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.AffineInterpolation

public section

/- Lemma 6.19a (Affine interpolation between E-points remains in E).
If two endpoint pairs belong to `Lorentz.embeddingRange d hd`, then at every time
strictly between their first coordinates, interpolation of the second coordinates
with the same affine parameter gives another point of the embedding range. -/
#check
  (Lorentz.affineInterpolation_mem_embeddingRange :
    ∀ (d : C0Seq) (hd : d ≠ 0) {P₀ P₁ P : ℝ} {N₀ N₁ : HilbertProd2 UnitL2},
      (P₀, N₀) ∈ Lorentz.embeddingRange d hd →
      (P₁, N₁) ∈ Lorentz.embeddingRange d hd →
      P ∈ Set.Ioo P₀ P₁ →
      (P, AffineMap.lineMap N₀ N₁ ((P - P₀) / (P₁ - P₀))) ∈
        Lorentz.embeddingRange d hd)
