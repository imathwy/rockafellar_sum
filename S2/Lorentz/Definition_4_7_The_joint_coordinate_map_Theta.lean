/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap
public import S2.PositiveOperator.Definition_3_9_A_missing_range_vector_and_its_coordinate_functional

/-!
# The Joint Coordinate Map

This module exposes the joint coordinate map and its fixed-direction formulas.
-/

/- Definition 4.7 (The joint coordinate map $\Theta$) -/
#check (L1Seq.jointCoordinateMap
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  L1Seq →L[ℝ] C0Seq × (UnitL2 × ℝ))

#check (L1Seq.jointCoordinateMap_apply
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ a : L1Seq,
    L1Seq.jointCoordinateMap
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) a =
      (L1Seq.positiveOperator a, L1Seq.intervalCoordinateOperator a,
        C0Seq.pairingL
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) a))
