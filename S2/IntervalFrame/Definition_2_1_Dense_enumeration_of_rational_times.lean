module

import ReasLib.Order.RationalTime

/- Definition 2.1 (Dense enumeration of rational times) (1): the fixed equivalence. -/
#check (rationalTimeEquiv : ℕ ≃ RationalTime)

/- Definition 2.1 (Dense enumeration of rational times) (2): the associated real sequence. -/
#check (rationalTime : ℕ → ℝ)

/- Definition 2.1 (Dense enumeration of rational times) (3): injectivity. -/
#check (rationalTime_injective : Function.Injective rationalTime)

/- Definition 2.1 (Dense enumeration of rational times) (4): interval membership. -/
#check (rationalTime_mem_Ioo : ∀ n : ℕ, rationalTime n ∈ Set.Ioo (0 : ℝ) 1)

/- Definition 2.1 (Dense enumeration of rational times) (5): exhaustive rational occurrence. -/
#check (exists_rationalTime_eq :
  ∀ q : RationalTime, ∃ n : ℕ, rationalTime n = (q.1 : ℝ))

/- Definition 2.1 (Dense enumeration of rational times) (6): arbitrarily late interval hits. -/
#check (exists_gt_rationalTime_mem_Ioo :
  ∀ {a b : ℝ}, a < b → Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1 →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ rationalTime n ∈ Set.Ioo a b)
