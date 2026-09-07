/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

import S2.Basic.Definition_1_4_Target_localization_sets_Localization

/-!
# Fixed Closed-Ball Constraint

This module exposes the fixed radius-`1 / 2` constraint set.
-/

/- Definition 7.9 (The fixed closed-ball constraint set):
The fixed constraint in real `c₀` is the radius-`1 / 2` closed ball centered at zero. -/
#check C0Seq.finalConstraint
#check C0Seq.mem_finalConstraint
#check C0Seq.finalConstraint_eq_smul_closedUnitBall
