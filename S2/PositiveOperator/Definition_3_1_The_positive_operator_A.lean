/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator

/-!
# The positive operator `A`

This source-facing module records the canonical positive operator and its
coordinate formula.
-/

/- Definition 3.1 (The positive operator $A$) -/
#check (L1Seq.positiveOperator : L1Seq →L[ℝ] C0Seq)
#check (L1Seq.positiveOperator_apply :
  ∀ (a : L1Seq) (n : ℕ),
    L1Seq.positiveOperator a n = rationalTime n * a n +
      2 * ∑' m : ℕ, if n < m then min (rationalTime n) (rationalTime m) * a m else 0)
