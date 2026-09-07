/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Dual

/-!
# The Dual of `C0Seq`

This module exposes the isometric linear identification of `C0Seq` duals with `L1Seq`.
-/

/- Infrastructure A.11 (Isometric identification c₀* ≃ ℓ¹) -/
#check (C0Seq.dualEquivL1 : StrongDual ℝ C0Seq ≃ₗᵢ[ℝ] L1Seq)

#check (C0Seq.dualEquivL1_apply :
  (φ : StrongDual ℝ C0Seq) →
    C0Seq.dualEquivL1 φ = C0Seq.dualCoefficients φ)

#check (C0Seq.dualEquivL1_apply_apply :
  (φ : StrongDual ℝ C0Seq) → (n : ℕ) →
    C0Seq.dualEquivL1 φ n = φ (c0Single n 1))

#check (C0Seq.dualEquivL1_symm_toLinearIsometry :
  C0Seq.dualEquivL1.symm.toLinearIsometry = C0Seq.l1ToDual)

#check (C0Seq.dualEquivL1_symm_apply :
  (a : L1Seq) → C0Seq.dualEquivL1.symm a = C0Seq.l1ToDual a)

#check (C0Seq.dualEquivL1_symm_apply_apply :
  (a : L1Seq) → (x : C0Seq) →
    C0Seq.dualEquivL1.symm a x = ∑' n : ℕ, x n * a n)
