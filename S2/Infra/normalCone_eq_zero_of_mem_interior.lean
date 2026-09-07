/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Convex.NormalCone

/-!
# Interior normal-cone infrastructure

This source-facing module records the canonical zero normal-cone result at
interior points.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.8 (Normal cone at an interior point): the normal cone of a set at
an interior point is the singleton containing zero. -/
#check (DualPairing.normalCone_eq_zero_of_mem_interior :
  ∀ (P : DualPairing X Xstar) {C : Set X} {x : X},
    x ∈ interior C → P.normalCone C x = {0})

end DualPairing
