/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Injective

/-!
# Injectivity of `V`

This source-facing module records the trivial-kernel property of the
interval-coordinate operator.
-/

/- Lemma 2.7 (Injectivity of $V$). The interval-coordinate operator has trivial kernel:
if `L1Seq.intervalCoordinateOperator a = 0`, then `a = 0`. -/
#check (L1Seq.intervalCoordinateOperator_injective :
  Function.Injective L1Seq.intervalCoordinateOperator)
