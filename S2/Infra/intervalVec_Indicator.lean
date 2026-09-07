/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalIndicator

/-!
# Interval-vector representatives

This module identifies interval vectors with their almost-everywhere indicator functions.
-/

#check (UnitL2.intervalVec : unitInterval → UnitL2)
#check (UnitL2.intervalVec_apply_ae :
  ∀ t : unitInterval,
    ∀ᵐ x : ℝ ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
      UnitL2.intervalVec t x =
        (Set.Ioo (0 : ℝ) t).indicator (fun _ ↦ (1 : ℝ)) x)
