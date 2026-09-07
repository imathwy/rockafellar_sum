module

public import ReasLib.Analysis.Sequence.L1Synthesis.Transpose

open scoped InnerProductSpace

universe u

/-
Infrastructure B.6 (Coordinate formula for the transpose of an ℓ¹ synthesis map):
the `n`th coordinate of the transposed Riesz functional is `⟪y, u n⟫_ℝ`.
-/
#check (L1Seq.paperTranspose_synthesis_single :
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K) (y : H) (n : ℕ),
    (L1Seq.synthesis u hu).paperTranspose ((InnerProductSpace.toDual ℝ H) y)
        (lp.single 1 n (1 : ℝ)) = ⟪y, u n⟫_ℝ)
