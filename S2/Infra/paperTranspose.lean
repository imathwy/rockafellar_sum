/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Transpose

/-!
# Typed paper transposes

This module records transpose conventions and coordinate formulas for maps out of `L1Seq`.
-/

public section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Infrastructure A.12 (Typed transpose conventions for maps out of ℓ¹) (1): the
paper-style transpose of a continuous linear map from `L1Seq`. -/
#check (ContinuousLinearMap.paperTranspose :
  (L1Seq →L[ℝ] E) → StrongDual ℝ E →L[ℝ] StrongDual ℝ L1Seq)

#check (ContinuousLinearMap.paperTranspose_apply :
  ∀ (T : L1Seq →L[ℝ] E) (φ : StrongDual ℝ E) (a : L1Seq),
    T.paperTranspose φ a = φ (T a))

/- Infrastructure A.12 (Typed transpose conventions for maps out of ℓ¹) (2): the
transpose of a map into `C0Seq`, reindexed through the canonical dual identification. -/
#check (ContinuousLinearMap.reindexedTranspose :
  (L1Seq →L[ℝ] C0Seq) → L1Seq →L[ℝ] StrongDual ℝ L1Seq)

#check (ContinuousLinearMap.reindexedTranspose_apply :
  ∀ (A : L1Seq →L[ℝ] C0Seq) (a : L1Seq),
    A.reindexedTranspose a = A.paperTranspose (C0Seq.dualEquivL1.symm a))

#check (ContinuousLinearMap.reindexedTranspose_apply_apply :
  ∀ (A : L1Seq →L[ℝ] C0Seq) (a b : L1Seq),
    A.reindexedTranspose a b = ∑' n : ℕ, A b n * a n)
