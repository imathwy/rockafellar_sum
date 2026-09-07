module

public import ReasLib.Analysis.Sequence.L1Synthesis
public import ReasLib.FunctionalAnalysis.SequenceSpace.L1.Transpose
public import Mathlib.Analysis.InnerProductSpace.Dual

open scoped InnerProductSpace

universe u

namespace L1Seq

/-- Evaluating the paper transpose of an `L1Seq` synthesis operator at a Riesz
functional and an ℓ¹ unit vector gives the corresponding inner product. -/
public theorem paperTranspose_synthesis_single
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K) (y : H) (n : ℕ) :
    (synthesis u hu).paperTranspose ((InnerProductSpace.toDual ℝ H) y)
        (lp.single 1 n (1 : ℝ)) = ⟪y, u n⟫_ℝ := by
  -- Expose transpose evaluation, the Riesz functional, and the synthesis series.
  rw [ContinuousLinearMap.paperTranspose_apply,
    InnerProductSpace.toDual_apply_apply, synthesis_apply, tsum_eq_single n]
  · -- The surviving coordinate has coefficient one.
    rw [lp.single_apply_self, one_smul]
  · -- Every off-diagonal coordinate contributes the zero vector.
    intro m hm
    simp only [lp.single_apply, Pi.single_apply, if_neg hm, zero_smul]

end L1Seq
