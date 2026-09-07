module

public import ReasLib.Analysis.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding

public section

namespace Lorentz

/-- If two points belong to a Lorentz embedding range, then synchronously
interpolating their time and spatial coordinates gives another point in the range. -/
theorem affineInterpolation_mem_embeddingRange
    (d : C0Seq) (hd : d ≠ 0) {P₀ P₁ P : ℝ} {N₀ N₁ : HilbertProd2 UnitL2}
    (h₀ : (P₀, N₀) ∈ embeddingRange d hd) (h₁ : (P₁, N₁) ∈ embeddingRange d hd)
    (hP : P ∈ Set.Ioo P₀ P₁) :
    (P, AffineMap.lineMap N₀ N₁ ((P - P₀) / (P₁ - P₀))) ∈ embeddingRange d hd := by
  -- Choose preimages of the endpoints and interpolate them with the same parameter.
  rw [mem_embeddingRange] at h₀ h₁ ⊢
  obtain ⟨z₀, hz₀⟩ := h₀
  obtain ⟨z₁, hz₁⟩ := h₁
  let c : ℝ := (P - P₀) / (P₁ - P₀)
  refine ⟨(1 - c) • z₀ + c • z₁, ?_⟩
  -- Linearity reduces the image equality to its time and spatial coordinates.
  rw [embedding_apply, map_add, map_smul, map_smul]
  rw [embedding_apply] at hz₀
  rw [embedding_apply] at hz₁
  apply Prod.ext
  · have hcoord₀ := congrArg Prod.fst hz₀
    have hcoord₁ := congrArg Prod.fst hz₁
    dsimp [embedding] at *
    rw [hcoord₀, hcoord₁]
    dsimp [c]
    have hden : P₁ - P₀ ≠ 0 :=
      ne_of_gt (sub_pos.mpr (lt_trans hP.1 hP.2))
    -- The normalized affine coefficients reproduce the chosen time coordinate.
    field_simp [hden]
    ring
  · have hcoord₀ := congrArg Prod.snd hz₀
    have hcoord₁ := congrArg Prod.snd hz₁
    dsimp [embedding] at *
    rw [map_add, map_smul, map_smul, hcoord₀, hcoord₁]
    -- The spatial affine combination is exactly the line-map formula.
    rw [AffineMap.lineMap_apply_module]

end Lorentz
