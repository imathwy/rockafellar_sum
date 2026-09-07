/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint.C0Range

/-!
# Vanishing Primitive Samples

This module exposes the convergence of primitive samples along rational times.
-/

public section

open Topology

/-
Lemma 2.11a (c₀ membership gives vanishing primitive samples): if the transpose
coordinate sequence of `y` lies in the canonical image of `C0Seq`, then the values of
`UnitL2.primitive y` at `rationalTime n` tend to zero.
-/
#check (UnitL2.primitive_rationalTime_tendsto_zero :
  ∀ (y : UnitL2), L1Seq.intervalCoordinateAdjoint y ∈ Set.range C0Seq.pairingL →
    Filter.Tendsto (fun n : ℕ ↦ UnitL2.primitive y (rationalTime n))
      Filter.atTop (𝓝 0))
