/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

import ReasLib.Order.RationalTime

/-!
# Rational-Time Tail Density

This module records tail density of the canonical rational-time enumeration.
-/

/- Lemma 2.2 (Tail density of the rational enumeration) -/
#check (exists_gt_rationalTime_mem_Ioo :
  ∀ {a b : ℝ}, a < b → Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1 →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ rationalTime n ∈ Set.Ioo a b)
