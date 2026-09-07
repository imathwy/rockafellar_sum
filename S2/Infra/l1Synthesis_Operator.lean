module

public import ReasLib.Analysis.Sequence.L1Synthesis

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (u : ℕ → H) {K : ℝ} (hu : ∀ n, ‖u n‖ ≤ K)

#check (L1Seq.synthesis u hu : L1Seq →L[ℝ] H)
#check (L1Seq.summable_norm_smul u hu :
  ∀ a : L1Seq, Summable (fun n ↦ ‖a n • u n‖))
#check (L1Seq.synthesis_apply u hu :
  ∀ a : L1Seq, L1Seq.synthesis u hu a = ∑' n, a n • u n)
#check (L1Seq.norm_synthesis_le u hu : ‖L1Seq.synthesis u hu‖ ≤ K)
