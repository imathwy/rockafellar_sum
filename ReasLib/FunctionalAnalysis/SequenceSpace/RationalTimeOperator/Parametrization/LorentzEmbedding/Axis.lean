/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.Kernel
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding

/-!
# Missing Lorentz axis

This module proves that nonzero points on the first-coordinate axis are absent
from the Lorentz embedding range.
-/

public section

namespace Lorentz

/-- No point on the nonzero first-coordinate axis belongs to the Lorentz embedding range. -/
theorem axis_not_mem_embeddingRange (d : C0Seq) (hd : d ≠ 0)
    (p : ℝ) (hp : p ≠ 0) :
    (p, 0) ∉ embeddingRange d hd := by
  -- Expose a source point whose two Lorentz coordinates form the alleged axis point.
  intro hmem
  rw [mem_embeddingRange] at hmem
  obtain ⟨z, hz⟩ := hmem
  rw [embedding_apply] at hz
  -- Project the pair equality to identify the positive and negative coordinates.
  have hP' := congrArg Prod.fst hz
  have hN' := congrArg Prod.snd hz
  have hN : negativeCoordinate d hd z = 0 := hN'
  -- Coordinate rigidity makes the positive coordinate vanish as well.
  have hP : positiveCoordinate d hd z = 0 :=
    positiveCoordinate_eq_zero_of_negativeCoordinate_eq_zero d hd z hN
  -- The first projection now gives `p = 0`, contradicting the axis hypothesis.
  exact hp (hP'.symm.trans hP)

end Lorentz
