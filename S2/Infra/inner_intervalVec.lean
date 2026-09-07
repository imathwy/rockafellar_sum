/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalIndicator

/-!
# Interval-indicator Gram infrastructure

This source-facing module records the canonical Gram and norm identities for
interval-indicator vectors.
-/

public section

open scoped InnerProductSpace

/- Infrastructure B.3 (Gram identity for interval indicators) (1).
The inner product of two interval-indicator vectors is the minimum of their endpoints. -/
#check (UnitL2.inner_intervalVec :
  ∀ s t : unitInterval,
    ⟪UnitL2.intervalVec s, UnitL2.intervalVec t⟫_ℝ = min (s : ℝ) (t : ℝ))

/- Infrastructure B.3 (Gram identity for interval indicators) (2).
The squared norm of an interval-indicator vector is its endpoint. -/
#check (UnitL2.norm_sq_intervalVec :
  ∀ t : unitInterval, ‖UnitL2.intervalVec t‖ ^ 2 = (t : ℝ))
