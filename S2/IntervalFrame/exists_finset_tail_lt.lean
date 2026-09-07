module

public import ReasLib.Analysis.Sequence.L1

public section

/- Lemma 2.7b (Finite-tail control for an ℓ¹ coefficient). For any positive
tolerance and prescribed index, an `L1Seq` has a finite set containing that
index outside of which the sum of the absolute values is below the tolerance. -/
#check (L1Seq.exists_finset_tail_lt :
  ∀ (a : L1Seq) (n₀ : ℕ) (ε : ℝ) (_ : 0 < ε),
    ∃ J : Finset ℕ, n₀ ∈ J ∧ (∑' n : {n // n ∉ J}, |a n|) < ε)
