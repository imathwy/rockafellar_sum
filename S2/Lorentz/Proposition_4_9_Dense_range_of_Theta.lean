/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.DenseRange

/-!
# Dense range of the joint-coordinate map

This module records density for the joint-coordinate map outside the positive-operator range.
-/

public section

/- Proposition 4.9 (Dense range of $\Theta$): the joint-coordinate map associated to any vector
outside the range of the positive operator has dense range. -/
#check (L1Seq.jointCoordinateMap_denseRange :
  (d : C0Seq) → d ∉ Set.range L1Seq.positiveOperator →
    DenseRange (L1Seq.jointCoordinateMap d))
