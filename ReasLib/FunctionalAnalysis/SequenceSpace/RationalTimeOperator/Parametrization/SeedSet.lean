/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Combinatorics.DetectorSchedule
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedDetector

/-!
# Detector component of the Lorentz seed set
-/

public section

namespace Lorentz

/-- The scheduled detector component of a Lorentz seed. The copy family is
indexed by the detector label and the remote-point index. -/
noncomputable def scheduledDetectorSet (d : C0Seq)
    (schedule : RepeatingSchedule DetectorTriple)
    (c : DetectorTriple → ℕ → L1Seq) : Set (C0Seq × L1Seq) :=
  {z | ∃ n : ℕ, z = seedDetectorPoint d
      (schedule.toFun n).p (schedule.toFun n).q
      (c (schedule.toFun n)) n}

/-- Every scheduled detector point belongs to the Lorentz carrier. -/
theorem scheduledDetectorSet_subset_carrier (d : C0Seq)
    (schedule : RepeatingSchedule DetectorTriple)
    (c : DetectorTriple → ℕ → L1Seq) :
    scheduledDetectorSet d schedule c ⊆ parametrizedSubspace d := by
  intro z hz
  rcases hz with ⟨n, rfl⟩
  exact seedDetectorPoint_mem d (schedule.toFun n).p (schedule.toFun n).q
    (c (schedule.toFun n)) n

/-- Every detector label occurs infinitely often in the scheduled seed family. -/
theorem scheduledDetectorSet_has_label
    (schedule : RepeatingSchedule DetectorTriple) (t : DetectorTriple) :
    Set.Infinite {n : ℕ | schedule.toFun n = t} := by
  exact schedule.infinite_fiber t

end Lorentz
