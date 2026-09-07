/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

/-!
# Summability of the c0-l1 pairing

This module records absolute summability and norm bounds for coordinatewise pairings.
-/

public section

/- Infrastructure A.6 (Absolute summability of the c₀–ℓ¹ pairing) (1): the
coordinatewise products of `x : C0Seq` and `a : L1Seq` are absolutely summable. -/
#check (C0Seq.summable_abs_mul :
  ∀ (x : C0Seq) (a : L1Seq), Summable (fun n : ℕ ↦ |x n * a n|))

/- Infrastructure A.6 (Absolute summability of the c₀–ℓ¹ pairing) (2): the
absolute value of the pairing is bounded by the product of the two norms. -/
#check (C0Seq.abs_tsum_mul_le :
  ∀ (x : C0Seq) (a : L1Seq), |∑' n : ℕ, x n * a n| ≤ ‖x‖ * ‖a‖)
