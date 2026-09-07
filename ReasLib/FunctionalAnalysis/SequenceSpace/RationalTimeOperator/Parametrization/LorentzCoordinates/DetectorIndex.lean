/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.Group.Sequences
public import ReasLib.Combinatorics.DetectorSchedule
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorScale

/-!
# Scheduled detector coordinates

This module evaluates detector families at the repeating schedule and records
their coordinate and pairing bounds.
-/

public section

open Topology

namespace Lorentz

/-- Evaluate a pair-indexed detector-point family at the pair in the `i`-th
scheduled detector triple. -/
noncomputable def scheduledDetectorPoint {d : C0Seq}
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d) (i n : ℕ) :
    parametrizedSubspace d :=
  h (DetectorTriple.schedule.toFun i).p (DetectorTriple.schedule.toFun i).q
    (DetectorTriple.schedule.toFun i).p_lt_q n

/-- The scheduled detector point is the given pair-indexed point at the scheduled
coordinates. -/
theorem scheduledDetectorPoint_apply {d : C0Seq}
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d) (i n : ℕ) :
    scheduledDetectorPoint h i n =
      h (DetectorTriple.schedule.toFun i).p (DetectorTriple.schedule.toFun i).q
        (DetectorTriple.schedule.toFun i).p_lt_q n := by
  -- Unfolding the scheduled evaluation exposes exactly the selected pair.
  rfl

/-- Pairwise convergence of the negative Lorentz coordinates restricts to every
scheduled detector pair. -/
theorem tendsto_negativeCoordinate_scheduledDetectorPoint
    (d : C0Seq) (hd : d ≠ 0)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    Filter.Tendsto
      (fun n ↦ negativeCoordinate d hd (scheduledDetectorPoint h i n))
      Filter.atTop (nhds 0) := by
  -- Specialize pairwise convergence and rewrite its sequence through the public evaluation rule.
  simpa only [scheduledDetectorPoint_apply] using
    (h_tendsto (DetectorTriple.schedule.toFun i).p
      (DetectorTriple.schedule.toFun i).q
      (DetectorTriple.schedule.toFun i).p_lt_q)

/-- After fixing the `i`-th scale, choose an index at least `i` where the
scaled negative Lorentz coordinate of the scheduled detector point is less
than half the `i`-th radius. -/
noncomputable def detectorIndex (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) : ℕ → ℕ :=
  fun i ↦ Classical.choose
    (exists_ge_scaled_norm_lt
      (fun n ↦ negativeCoordinate d hd (scheduledDetectorPoint h i n))
      (tendsto_negativeCoordinate_scheduledDetectorPoint d hd h h_tendsto i)
      (detectorScale d hd h_missing i) (DetectorTriple.rightRadius i / 2)
      (detectorScale_pos d hd h_missing i) (DetectorTriple.rightRadius_half_pos i) i)

/-- The chosen detector index is late enough and satisfies the required scaled
negative-coordinate bound. -/
theorem detectorIndex_spec (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    i ≤ detectorIndex d hd h_missing h h_tendsto i ∧
    detectorScale d hd h_missing i *
          ‖negativeCoordinate d hd
            (scheduledDetectorPoint h i
              (detectorIndex d hd h_missing h h_tendsto i))‖ <
        DetectorTriple.rightRadius i / 2 := by
  -- Unfold the choice once, then retain both properties supplied by the selection theorem.
  unfold detectorIndex
  exact Classical.choose_spec
    (exists_ge_scaled_norm_lt
      (fun n ↦ negativeCoordinate d hd (scheduledDetectorPoint h i n))
      (tendsto_negativeCoordinate_scheduledDetectorPoint d hd h h_tendsto i)
      (detectorScale d hd h_missing i) (DetectorTriple.rightRadius i / 2)
      (detectorScale_pos d hd h_missing i) (DetectorTriple.rightRadius_half_pos i) i)

/-- Every selected detector index is at least its schedule index. -/
theorem le_detectorIndex (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    i ≤ detectorIndex d hd h_missing h h_tendsto i := by
  -- The lower bound is the first component of the stable choice specification.
  exact (detectorIndex_spec d hd h_missing h h_tendsto i).1

/-- At the selected index, the scaled negative-coordinate norm is less than half
the scheduled radius. -/
theorem scaled_norm_detectorIndex_lt (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    detectorScale d hd h_missing i *
        ‖negativeCoordinate d hd
          (scheduledDetectorPoint h i
            (detectorIndex d hd h_missing h h_tendsto i))‖ <
      DetectorTriple.rightRadius i / 2 := by
  -- The scaled estimate is the second component of the stable choice specification.
  exact (detectorIndex_spec d hd h_missing h h_tendsto i).2

end Lorentz
