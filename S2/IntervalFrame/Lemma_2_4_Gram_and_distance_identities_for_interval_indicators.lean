/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalIndicator

/-!
# Gram and distance identities

This source-facing module records the canonical Gram, norm, and distance
identities for interval-indicator vectors.
-/

@[expose] public section

open scoped InnerProductSpace

/- Lemma 2.4 (Gram and distance identities for interval indicators) (1).
For `s, t ∈ (0, 1)`, the Gram entry of the interval-indicator vectors is `min s t`. -/
#check
  (UnitL2.inner_intervalVec_of_mem_Ioo :
    ∀ (s t : unitInterval),
      (s : ℝ) ∈ Set.Ioo 0 1 →
      (t : ℝ) ∈ Set.Ioo 0 1 →
      ⟪UnitL2.intervalVec s, UnitL2.intervalVec t⟫_ℝ = min (s : ℝ) (t : ℝ))

/- Lemma 2.4 (Gram and distance identities for interval indicators) (2).
For `t ∈ (0, 1)`, the norm of the interval-indicator vector is `Real.sqrt t`. -/
#check
  (UnitL2.norm_intervalVec_of_mem_Ioo :
    ∀ (t : unitInterval),
      (t : ℝ) ∈ Set.Ioo 0 1 →
      ‖UnitL2.intervalVec t‖ = Real.sqrt (t : ℝ))

/- Lemma 2.4 (Gram and distance identities for interval indicators) (3).
For `t ∈ (0, 1)`, the norm of the interval-indicator vector is at most one. -/
#check
  (UnitL2.norm_intervalVec_le_one_of_mem_Ioo :
    ∀ (t : unitInterval),
      (t : ℝ) ∈ Set.Ioo 0 1 →
      ‖UnitL2.intervalVec t‖ ≤ 1)

/- Lemma 2.4 (Gram and distance identities for interval indicators) (4).
For `s, t ∈ (0, 1)`, the distance of their interval-indicator vectors is
`Real.sqrt |s - t|`. -/
#check
  (UnitL2.norm_sub_intervalVec_of_mem_Ioo :
    ∀ (s t : unitInterval),
      (s : ℝ) ∈ Set.Ioo 0 1 →
      (t : ℝ) ∈ Set.Ioo 0 1 →
      ‖UnitL2.intervalVec s - UnitL2.intervalVec t‖ =
        Real.sqrt |(s : ℝ) - (t : ℝ)|)
