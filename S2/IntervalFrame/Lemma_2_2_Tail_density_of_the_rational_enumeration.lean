module

import ReasLib.Order.RationalTime

/- Lemma 2.2 (Tail density of the rational enumeration) -/
#check (exists_gt_rationalTime_mem_Ioo :
  ∀ {a b : ℝ}, a < b → Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1 →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ rationalTime n ∈ Set.Ioo a b)
