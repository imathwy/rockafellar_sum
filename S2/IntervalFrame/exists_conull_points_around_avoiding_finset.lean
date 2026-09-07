/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.Measure.Lebesgue.Conull

/-!
# Conull points around finite exclusions

This module provides two nearby conull points while avoiding a finite set of breakpoints.
-/

/- Lemma 2.7c (Two-sided conull points avoiding finitely many breakpoints) -/
#check (Real.exists_conull_points_around_avoiding_finset :
  ∀ {E : Set ℝ},
    E ⊆ Set.Ioo (0 : ℝ) 1 →
    MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 \ E) = 0 →
    ∀ {t : ℝ}, t ∈ Set.Ioo 0 1 →
    ∀ (F : Finset ℝ), t ∉ F →
    ∀ (ε : ℝ), 0 < ε →
      ∃ sLeft ∈ E ∩ Set.Ioo (t - ε) t,
        ∃ sRight ∈ E ∩ Set.Ioo t (t + ε),
          ∀ x ∈ F, x ∉ Set.Ioo sLeft sRight)
