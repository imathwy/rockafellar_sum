/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator

/-!
# Boundedness and `C0Seq`-valuedness of `A`

This source-facing module records the coordinate majorant and its convergence
to zero.
-/

public section

/- Lemma 3.2 ($A$ is bounded and $c_0$-valued) (1): each coordinate of
`positiveOperator a` is dominated by `|a n|` plus twice its strict upper
absolute tail. -/
#check (L1Seq.abs_positiveOperator_apply_le :
  ∀ (a : L1Seq) (n : ℕ),
    |L1Seq.positiveOperator a n| ≤
      |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0)

/- Lemma 3.2 ($A$ is bounded and $c_0$-valued) (2): the coordinate majorant
tends to zero. -/
#check (L1Seq.positiveOperatorCoordBound_tendsto :
  ∀ a : L1Seq,
    Filter.Tendsto
      (fun n : ℕ ↦ |a n| + 2 * ∑' m : ℕ, if n < m then |a m| else 0)
      Filter.atTop (nhds 0))

/- Lemma 3.2 ($A$ is bounded and $c_0$-valued) (3): `positiveOperator` is a
bounded linear map from `L1Seq` into `C0Seq`. -/
#check (L1Seq.positiveOperator : L1Seq →L[ℝ] C0Seq)

/- Lemma 3.2 ($A$ is bounded and $c_0$-valued) (4): the operator norm of
`positiveOperator` is at most `3`. -/
#check (L1Seq.norm_positiveOperator_le : ‖L1Seq.positiveOperator‖ ≤ 3)
