/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPoint.Detection

/-!
# Detection from vanishing coordinates

This module records detector readings retained by admissible remote sequences.
-/

public section

open Topology

/- Theorem 5.11 (Vanishing-coordinate detectors retain the full detection reading) (1):
pairing with an admissible remote detector sequence tends to its detector-functional
reading. -/
#check (Lorentz.remoteDetectorPoint_pairing_tendsto :
  ∀ (d : C0Seq) (w : C0Seq × L1Seq) (p q : ℕ), p < q →
    ∀ c : ℕ → L1Seq,
      (∀ n,
        Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
          ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
          ‖L1Seq.intervalCoordinateOperator (c n) -
              L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
            1 / (n + 1 : ℝ)) →
        Filter.Tendsto
          (fun n ↦ C0Seq.symmetricForm w (Lorentz.remoteDetectorPoint d p q c n))
          Filter.atTop (𝓝 (Lorentz.detectorFunctional d p q w)))

/- Theorem 5.11 (Vanishing-coordinate detectors retain the full detection reading) (2):
every point outside `Lorentz.parametrizedSubspace d` admits one remote detector sequence
whose negative Lorentz coordinate tends to zero while its pairing tends to a nonzero
detector reading. -/
#check (Lorentz.exists_remoteDetectorPoint_detection_tendsto :
  ∀ (d : C0Seq) (hd : d ≠ 0) (w : C0Seq × L1Seq),
    w ∉ Lorentz.parametrizedSubspace d →
      ∃ p q : ℕ, ∃ c : ℕ → L1Seq,
        (p < q ∧ ∀ n,
          Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
            ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
            ‖L1Seq.intervalCoordinateOperator (c n) -
                L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
              1 / (n + 1 : ℝ)) ∧
          (Lorentz.detectorFunctional d p q w ≠ 0 ∧
            Filter.Tendsto
              (fun n ↦
                (Lorentz.negativeCoordinate d hd
                    (Lorentz.remoteDetectorPoint d p q c n),
                  C0Seq.symmetricForm w (Lorentz.remoteDetectorPoint d p q c n)))
              Filter.atTop (𝓝 (0, Lorentz.detectorFunctional d p q w))))
