/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Proportionality

/-!
# Proportionality from vanishing determinants

This module exposes the scalar-proportionality criterion for coordinate determinants.
-/

public section

/- Lemma 5.4a (All two-by-two determinants zero imply proportionality): if every
ordered two-coordinate determinant of nonzero `d` and `r` vanishes, then `r` is a real
scalar multiple of `d`. -/
#check (C0Seq.eq_smul_of_all_twoDet_eq_zero :
  ∀ (d r : C0Seq), d ≠ 0 →
    (∀ p q : ℕ, p < q → d p * r q - d q * r p = 0) →
      ∃ s : ℝ, r = s • d)
