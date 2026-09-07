/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Combinatorics.DetectorTriple
public import ReasLib.Data.Countable.RepeatingSchedule

/-!
# Repeating detector schedules

This module specializes repeating schedules to the finite detector-triple
type.
-/

public section

namespace DetectorTriple

/-- An explicit schedule of detector triples in which every triple repeats infinitely often. -/
noncomputable def schedule : RepeatingSchedule DetectorTriple :=
  RepeatingSchedule.ofCountable DetectorTriple

/-- Every detector triple occurs infinitely often in `schedule`. -/
theorem schedule_infinite_fiber (t : DetectorTriple) :
    Set.Infinite {i | schedule.toFun i = t} := by
  -- The generic repeating-schedule invariant supplies infinitely many occurrences of `t`.
  exact RepeatingSchedule.infinite_fiber schedule t

end DetectorTriple
