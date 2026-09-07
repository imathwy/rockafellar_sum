/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Combinatorics.DetectorSchedule

/-!
# Detector Schedule

This module exposes countability and infinite repetition of detector triples.
-/

public section

#check (inferInstance : Countable DetectorTriple)
#check (inferInstance : Nonempty DetectorTriple)

/- Lemma 6.8a (Countability and infinite repetition of detector triples): an explicit
schedule of zero-based triples `p < q` with sign `±1` in which every triple repeats
infinitely often. -/
#check (DetectorTriple.schedule : RepeatingSchedule DetectorTriple)

#check (DetectorTriple.schedule_infinite_fiber :
  ∀ t : DetectorTriple, Set.Infinite {i | DetectorTriple.schedule.toFun i = t})
