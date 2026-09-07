module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPairing

public section

open Topology

/-
Lemma 5.11a (Limit of the expanded detector pairing): for an admissible
remote-copy sequence, pairing with its remote detector points tends to the
two-coordinate detector functional.
-/
#check (Lorentz.remoteDetectorPoint_pairing_tendsto :
  ∀ (d : C0Seq) (w : C0Seq × L1Seq) (p q : ℕ), p < q → ∀ (c : ℕ → L1Seq),
    (∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) →
      Filter.Tendsto
        (fun n ↦ C0Seq.symmetricForm w (Lorentz.remoteDetectorPoint d p q c n))
        Filter.atTop (𝓝 (Lorentz.detectorFunctional d p q w)))
