/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.RationalIntervalIndicator

/-!
# Rational interval indicator vectors

This source-facing module records the rational-time interval-indicator
sequence and its representative formula.
-/

open MeasureTheory

#check (UnitL2.rationalIntervalVec : ℕ → UnitL2)
#check (UnitL2.rationalIntervalVec_apply_ae :
  ∀ n : ℕ,
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      UnitL2.rationalIntervalVec n x =
        (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) x)
