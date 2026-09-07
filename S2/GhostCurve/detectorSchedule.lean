module

public import ReasLib.Combinatorics.DetectorSchedule

public section

#check (inferInstance : Countable DetectorTriple)
#check (inferInstance : Nonempty DetectorTriple)

/- Lemma 6.8a (Countability and infinite repetition of detector triples): an explicit
schedule of zero-based triples `p < q` with sign `±1` in which every triple repeats
infinitely often. -/
#check (DetectorTriple.schedule : RepeatingSchedule DetectorTriple)

#check (DetectorTriple.schedule_infinite_fiber :
  ∀ t : DetectorTriple, Set.Infinite {i | DetectorTriple.schedule.toFun i = t})
