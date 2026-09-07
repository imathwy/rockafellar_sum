module

public import ReasLib.Combinatorics.DetectorTriple
public import ReasLib.Data.Countable.RepeatingSchedule

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
