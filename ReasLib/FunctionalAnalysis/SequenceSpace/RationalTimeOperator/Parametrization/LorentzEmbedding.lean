module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates

public section

noncomputable section

namespace Lorentz

/-- The Lorentz embedding pairs the positive and negative coordinates. -/
noncomputable def embedding (d : C0Seq) (hd : d ≠ 0) :
    parametrizedSubspace d →ₗ[ℝ] ℝ × HilbertProd2 UnitL2 :=
  (positiveCoordinate d hd).prod (negativeCoordinate d hd)

/-- The Lorentz embedding evaluates to the pair of Lorentz coordinates. -/
@[simp]
theorem embedding_apply (d : C0Seq) (hd : d ≠ 0) (z : parametrizedSubspace d) :
    embedding d hd z = (positiveCoordinate d hd z, negativeCoordinate d hd z) := by
  -- Evaluating the product linear map exposes its two coordinate maps.
  rfl

/-- The image of the Lorentz embedding as a real submodule. -/
noncomputable def embeddingRange (d : C0Seq) (hd : d ≠ 0) :
    Submodule ℝ (ℝ × HilbertProd2 UnitL2) :=
  (embedding d hd).range

/-- Membership in the Lorentz embedding range is witnessed by a source point. -/
theorem mem_embeddingRange (d : C0Seq) (hd : d ≠ 0)
    (y : ℝ × HilbertProd2 UnitL2) :
    y ∈ embeddingRange d hd ↔
      ∃ z : parametrizedSubspace d, embedding d hd z = y := by
  -- Range membership and an explicit preimage carry the same witness.
  constructor
  · intro hy
    rcases hy with ⟨z, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz⟩

end Lorentz
