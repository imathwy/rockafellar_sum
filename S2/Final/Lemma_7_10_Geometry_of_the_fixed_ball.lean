/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.Localization

/-!
# Geometry of the Fixed Ball

This module exposes nonemptiness, closedness, convexity, and interior facts.
-/

public section

open scoped ZeroAtInfty

/- Lemma 7.10 (Geometry of the fixed ball) (1):
The fixed constraint set is nonempty. -/
#check (C0Seq.nonempty_finalConstraint : Set.Nonempty C0Seq.finalConstraint)

/- Lemma 7.10 (Geometry of the fixed ball) (2):
The fixed constraint set is closed. -/
#check (C0Seq.isClosed_finalConstraint : IsClosed C0Seq.finalConstraint)

/- Lemma 7.10 (Geometry of the fixed ball) (3):
The fixed constraint set is convex. -/
#check (C0Seq.convex_finalConstraint : Convex ℝ C0Seq.finalConstraint)

/- Lemma 7.10 (Geometry of the fixed ball) (4):
Zero lies in the interior of the fixed constraint set. -/
#check (C0Seq.zero_mem_interior_finalConstraint :
  (0 : C₀(ℕ, ℝ)) ∈ interior C0Seq.finalConstraint)

/- Lemma 7.10 (Geometry of the fixed ball) (5):
The fixed constraint set is contained in the local open unit ball. -/
#check (C0Seq.finalConstraint_subset_localOpenUnitBall :
  C0Seq.finalConstraint ⊆ C0Seq.localOpenUnitBall)
