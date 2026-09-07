module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Single

public section

/- Infrastructure A.4 (The standard coordinate vectors in c₀): the element of `C0Seq`
whose value is `r` at coordinate `n` and zero at every other coordinate. -/
#check (c0Single : ℕ → ℝ → C0Seq)

#check (c0Single_apply :
  (n : ℕ) → (r : ℝ) → (m : ℕ) →
    c0Single n r m = if m = n then r else 0)

#check (c0Single_hasFiniteSupport :
  (n : ℕ) → (r : ℝ) → (fun m ↦ c0Single n r m).HasFiniteSupport)

#check (norm_c0Single :
  (n : ℕ) → (r : ℝ) → ‖c0Single n r‖ = |r|)
