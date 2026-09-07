module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteDetectorDifference
public import S2.Detector.Construction_5_6_Remote_copies_of_a_two_coordinate_detector_Sequence
public import S2.Detector.Lemma_5_3_Basic_properties_of_b_pq
public import S2.Detector.pairing_remoteSupport_tendsto_zero

public section

open Topology

/- Lemma 5.7 (Asymptotics of the remote-copy differences) (1): the norm of the
interval-coordinate image of the remote-copy difference tends to zero. -/
#check (L1Seq.remoteDetectorDifference_norm_image_tendsto_zero
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (p q : ℕ), p < q → ∀ (c : ℕ → L1Seq),
    (∀ n,
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
          1 / (n + 1 : ℝ)) →
      Filter.Tendsto
        (fun n ↦
          ‖L1Seq.intervalCoordinateOperator
            (L1Seq.remoteDetectorDifference
              (ContinuousLinearMap.unitVectorOutsideRange
                L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q c n)‖)
        Filter.atTop (𝓝 0))

/- Lemma 5.7 (Asymptotics of the remote-copy differences) (2): pairing the
remote-copy difference with the selected vector is the negative pairing with
the corresponding remote copy. -/
#check (L1Seq.remoteDetectorDifference_pairing_self
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (p q : ℕ), p < q → ∀ (c : ℕ → L1Seq) (n : ℕ),
    C0Seq.pairingL
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
        (L1Seq.remoteDetectorDifference
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q c n) =
      -C0Seq.pairingL
        (ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) (c n))

/- Lemma 5.7 (Asymptotics of the remote-copy differences) (3): pairing the
remote-copy difference with the selected vector tends to zero. -/
#check (L1Seq.remoteDetectorDifference_pairing_self_tendsto_zero
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (p q : ℕ), p < q → ∀ (c : ℕ → L1Seq),
    (∀ n,
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
          1 / (n + 1 : ℝ)) →
      Filter.Tendsto
        (fun n ↦ C0Seq.pairingL
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
          (L1Seq.remoteDetectorDifference
            (ContinuousLinearMap.unitVectorOutsideRange
              L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q c n))
        Filter.atTop (𝓝 0))

/- Lemma 5.7 (Asymptotics of the remote-copy differences) (4): pairing the
remote-copy difference with any `x : C0Seq` tends to its pairing with the
selected two-coordinate determinant vector. -/
#check (L1Seq.remoteDetectorDifference_pairing_tendsto
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (p q : ℕ), p < q → ∀ (c : ℕ → L1Seq),
    (∀ n,
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
          1 / (n + 1 : ℝ)) →
      ∀ x : C0Seq,
        Filter.Tendsto
          (fun n ↦ C0Seq.pairingL x
            (L1Seq.remoteDetectorDifference
              (ContinuousLinearMap.unitVectorOutsideRange
                L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q c n))
          Filter.atTop
            (𝓝 (C0Seq.pairingL x
              (L1Seq.twoDet
                (ContinuousLinearMap.unitVectorOutsideRange
                  L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) p q))))
