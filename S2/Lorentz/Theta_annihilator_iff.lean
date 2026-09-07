/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator
public import S2.Lorentz.Definition_4_7_The_joint_coordinate_map_Theta

/-!
# Typed annihilator equation for the joint-coordinate map

This module exposes the canonical three-coordinate annihilator characterization
for the fixed joint-coordinate map.
-/

/- Lemma 4.8a (Typed product-functional annihilator equation): under the canonical
dual identifications, `(b, y, lam)` annihilates the range of the fixed joint coordinate
map exactly when its three typed transpose coordinates sum to zero. -/
#check (L1Seq.jointCoordinateMap_annihilator_iff
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (b : L1Seq) (y : UnitL2) (lam : ℝ),
    ContinuousLinearMap.dualProdMap
        ((C0Seq.dualEquivL1).symm b, (InnerProductSpace.toDual ℝ UnitL2) y, lam) ∈
      StrongDual.polarSubmodule ℝ
        (L1Seq.jointCoordinateMap
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)).range ↔
        L1Seq.positiveOperator.reindexedTranspose b +
            L1Seq.intervalCoordinateAdjoint y +
            lam • C0Seq.pairingL
              (ContinuousLinearMap.unitVectorOutsideRange
                L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) = 0)
