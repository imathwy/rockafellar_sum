/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap

/-!
# Joint Coordinate Map API

This module exposes the joint coordinate operator and its evaluation formula.
-/

#check (L1Seq.jointCoordinateMap :
  C0Seq → L1Seq →L[ℝ] C0Seq × (UnitL2 × ℝ))
#check (L1Seq.jointCoordinateMap_apply :
  ∀ (d : C0Seq) (a : L1Seq),
    L1Seq.jointCoordinateMap d a =
      (L1Seq.positiveOperator a, L1Seq.intervalCoordinateOperator a,
        C0Seq.pairingL d a))
