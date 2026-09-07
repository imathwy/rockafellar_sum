/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

/-!
# Joint coordinate maps

This module bundles positive, interval, and parametrizing-pairing coordinates
into one continuous linear map.
-/

public section

noncomputable section

namespace L1Seq

/-- The joint map recording the positive, interval, and `d`-pairing coordinates. -/
noncomputable def jointCoordinateMap (d : C0Seq) :
    L1Seq →L[ℝ] C0Seq × (UnitL2 × ℝ) :=
  positiveOperator.prod (intervalCoordinateOperator.prod (C0Seq.pairingL d))

/-- Evaluating `jointCoordinateMap` gives its positive, interval, and pairing coordinates. -/
@[simp]
theorem jointCoordinateMap_apply (d : C0Seq) (a : L1Seq) :
    jointCoordinateMap d a =
      (positiveOperator a, intervalCoordinateOperator a, C0Seq.pairingL d a) := by
  -- Evaluate the two nested product maps to expose their three coordinates.
  rfl

end L1Seq
