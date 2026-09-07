module

import ReasLib.Analysis.C0Seq.Localization

open scoped ZeroAtInfty

/- Definition 1.4 (Target localization sets) (1): the local open unit ball `U`. -/
#check (C0Seq.localOpenUnitBall : Set C₀(ℕ, ℝ))

/- Definition 1.4 (Target localization sets) (2): the final constraint `C₀`. -/
#check (C0Seq.finalConstraint : Set C₀(ℕ, ℝ))
