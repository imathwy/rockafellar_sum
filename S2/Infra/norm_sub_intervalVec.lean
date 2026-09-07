/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalIndicator

/-!
# Distances between interval indicators

This module exposes the squared-distance and distance formulas for unit-interval
indicator vectors.
-/

public section

/- Infrastructure B.4 (Distance identity for interval indicators) (1).
The squared distance between two interval-indicator vectors is the absolute
difference of their endpoints. -/
#check (UnitL2.norm_sub_intervalVec_sq :
  ∀ s t : unitInterval,
    ‖UnitL2.intervalVec s - UnitL2.intervalVec t‖ ^ 2 = |(s : ℝ) - (t : ℝ)|)

/- Infrastructure B.4 (Distance identity for interval indicators) (2).
The distance between two interval-indicator vectors is the square root of the
absolute difference of their endpoints. -/
#check (UnitL2.norm_sub_intervalVec :
  ∀ s t : unitInterval,
    ‖UnitL2.intervalVec s - UnitL2.intervalVec t‖ = Real.sqrt |(s : ℝ) - (t : ℝ)|)
