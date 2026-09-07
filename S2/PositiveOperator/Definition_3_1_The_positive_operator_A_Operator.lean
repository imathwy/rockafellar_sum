/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator

/-!
# Positive operator object

This source-facing module records the bundled positive operator and its
coordinate bounds.
-/

#check (L1Seq.positiveOperator : L1Seq →L[ℝ] C0Seq)
#check (L1Seq.positiveOperator_apply :
  ∀ (a : L1Seq) (n : ℕ),
    L1Seq.positiveOperator a n = rationalTime n * a n +
      2 * ∑' m : ℕ, if n < m then min (rationalTime n) (rationalTime m) * a m else 0)
#check (L1Seq.abs_positiveOperator_apply_le :
  ∀ (a : L1Seq) (n : ℕ),
    |L1Seq.positiveOperator a n| ≤ |a n| +
      2 * ∑' m : ℕ, if n < m then |a m| else 0)
#check (L1Seq.norm_positiveOperator_le : ‖L1Seq.positiveOperator‖ ≤ 3)
