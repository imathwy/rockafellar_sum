/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.Integrable

/-!
# Integrability of UnitL2 representatives

This module records integrability and L2 norm bounds on the unit interval.
-/

@[expose] public section

open MeasureTheory

/- Infrastructure B.7 (L² functions on a finite interval are integrable) (1).
The canonical function representative of a real `UnitL2` vector is integrable on the
unit interval. -/
#check (UnitL2.integrable_coeFn :
  ∀ f : UnitL2, Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)))

/- Infrastructure B.7 (L² functions on a finite interval are integrable) (2).
The integral of the pointwise norm of a real `UnitL2` vector is bounded by its `L²`
norm. -/
#check (UnitL2.integral_norm_le_norm :
  ∀ f : UnitL2, (∫ x, ‖f x‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤ ‖f‖)
