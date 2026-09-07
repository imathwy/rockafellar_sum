module

public import ReasLib.Analysis.C0Seq.NormalCone

public section

open scoped ZeroAtInfty

/- Lemma 7.12a (The fixed ball is a nonempty closed convex set with known interior) (1):
The fixed constraint set is nonempty. -/
#check (C0Seq.nonempty_finalConstraint : Set.Nonempty C0Seq.finalConstraint)

/- Lemma 7.12a (The fixed ball is a nonempty closed convex set with known interior) (2):
The fixed constraint set is closed. -/
#check (C0Seq.isClosed_finalConstraint : IsClosed C0Seq.finalConstraint)

/- Lemma 7.12a (The fixed ball is a nonempty closed convex set with known interior) (3):
The fixed constraint set is convex. -/
#check (C0Seq.convex_finalConstraint : Convex ℝ C0Seq.finalConstraint)

/- Lemma 7.12a (The fixed ball is a nonempty closed convex set with known interior) (4):
The domain of the normal cone of the fixed constraint is the constraint itself. -/
#check (C0Seq.normalConeDom_finalConstraint :
  ∀ P : DualPairing C₀(ℕ, ℝ) L1Seq,
    P.normalConeDom C0Seq.finalConstraint = C0Seq.finalConstraint)

/- Lemma 7.12a (The fixed ball is a nonempty closed convex set with known interior) (5):
Zero lies in the interior of the fixed constraint set. -/
#check (C0Seq.zero_mem_interior_finalConstraint :
  (0 : C₀(ℕ, ℝ)) ∈ interior C0Seq.finalConstraint)

/- Lemma 7.12a (The fixed ball is a nonempty closed convex set with known interior) (6):
The normal cone of the fixed constraint at zero is the singleton containing zero. -/
#check (C0Seq.normalCone_finalConstraint_zero :
  ∀ P : DualPairing C₀(ℕ, ℝ) L1Seq,
    P.normalCone C0Seq.finalConstraint (0 : C₀(ℕ, ℝ)) = {0})
