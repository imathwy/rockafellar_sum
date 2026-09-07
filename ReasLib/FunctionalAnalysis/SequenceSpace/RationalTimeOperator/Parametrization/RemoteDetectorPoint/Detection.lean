module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorCoordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPairing

public section

open Topology

namespace Lorentz

/-- Every point outside a nontrivial parametrized subspace admits an admissible
remote-detector sequence whose negative coordinate vanishes while its pairing
converges to a nonzero detector-functional reading. -/
theorem exists_remoteDetectorPoint_detection_tendsto
    (d : C0Seq) (hd : d ≠ 0) (w : C0Seq × L1Seq)
    (hw : w ∉ parametrizedSubspace d) :
    ∃ p q : ℕ, ∃ c : ℕ → L1Seq,
      (p < q ∧ ∀ n,
        Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
          ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
          ‖L1Seq.intervalCoordinateOperator (c n) -
              L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
            1 / (n + 1 : ℝ)) ∧
        (detectorFunctional d p q w ≠ 0 ∧
          Filter.Tendsto
            (fun n ↦
              (negativeCoordinate d hd (remoteDetectorPoint d p q c n),
                C0Seq.symmetricForm w (remoteDetectorPoint d p q c n)))
            Filter.atTop (𝓝 (0, detectorFunctional d p q w))) := by
  -- Select two ordered coordinates on which the residual detector reading is nonzero.
  obtain ⟨p, q, hpq, hdet⟩ := exists_detectorFunctional_ne_zero d w hd hw
  -- Choose one admissible family of remote copies for this fixed detector.
  obtain ⟨c, hcopy⟩ := L1Seq.exists_remoteDetectorCopy d p q hpq
  refine ⟨p, q, c, ⟨hpq, hcopy⟩, ⟨hdet, ?_⟩⟩
  -- Combine vanishing of the negative coordinate with convergence of the pairing.
  simpa only [nhds_prod_eq] using
    (negativeCoordinate_remoteDetectorPoint_tendsto_zero d hd p q hpq c hcopy).prodMk
      (remoteDetectorPoint_pairing_tendsto d w p q hpq c hcopy)

end Lorentz
