/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

import ReasLib.Analysis.C0Seq.Localization

/-!
# Target localization sets

This source-facing module records the local open unit ball and the final
closed-ball constraint.
-/

open scoped ZeroAtInfty

/- Definition 1.4 (Target localization sets) (1): the local open unit ball `U`. -/
#check (C0Seq.localOpenUnitBall : Set C₀(ℕ, ℝ))

/- Definition 1.4 (Target localization sets) (2): the final constraint `C₀`. -/
#check (C0Seq.finalConstraint : Set C₀(ℕ, ℝ))
