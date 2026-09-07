/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteCopySequence
public import S2.PositiveOperator.Definition_3_9_A_missing_range_vector_and_its_coordinate_functional

/-!
# Remote copies of a two-coordinate detector

This source-facing module records the canonical remote-copy existence
statement for the distinguished determinant vector.
-/

/- Construction 5.6 (Remote copies of a two-coordinate detector): for fixed
coordinates `p < q`, choose equal-norm copies of the distinguished determinant
vector, supported beyond each index and with interval-coordinate error less than
`1 / (n + 1 : ℝ)`. -/
#check (L1Seq.exists_remoteDetectorCopy
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (p q : ℕ), p < q →
    ∃ c : ℕ → L1Seq, ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ =
          ‖L1Seq.twoDet
            (ContinuousLinearMap.unitVectorOutsideRange
              L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator
              (L1Seq.twoDet
                (ContinuousLinearMap.unitVectorOutsideRange
                  L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q)‖ <
          1 / (n + 1 : ℝ))

#check (L1Seq.remoteDetectorDifference
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ℕ → ℕ → (ℕ → L1Seq) → ℕ → L1Seq)

#check (L1Seq.remoteDetectorDifference_apply
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    L1Seq.remoteDetectorDifference
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q c n =
      L1Seq.twoDet
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q -
        c n)
