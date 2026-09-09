/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPoint
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPairing

/-!
# Detector points for the Lorentz seed construction

This module gives the seed construction a small interface for its remote
detector points. The pointwise construction remains hidden behind this API.
-/

public section

open Topology

namespace Lorentz

/-- A remote detector point associated with an ordered detector pair and a
copy family. -/
noncomputable def seedDetectorPoint (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    parametrizedSubspace d :=
  remoteDetectorPoint d p q c n

/-- The remote detector point has the detector-functional pairing limit required
by the seed polar argument. -/
theorem seedDetectorPoint_pairing_tendsto
    (d : C0Seq) (w : C0Seq × L1Seq) (p q : ℕ) (h_pq : p < q)
    (c : ℕ → L1Seq)
    (h_copy : ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) :
    Filter.Tendsto
      (fun n ↦ C0Seq.symmetricForm w (seedDetectorPoint d p q c n))
      Filter.atTop (𝓝 (detectorFunctional d p q w)) := by
  simpa only [seedDetectorPoint] using
    (remoteDetectorPoint_pairing_tendsto d w p q h_pq c h_copy)

/-- Every seed detector point lies in the parametrized Lorentz carrier. -/
theorem seedDetectorPoint_mem
    (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    (seedDetectorPoint d p q c n : C0Seq × L1Seq) ∈ parametrizedSubspace d := by
  exact (seedDetectorPoint d p q c n).property

end Lorentz
