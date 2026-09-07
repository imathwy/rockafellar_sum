/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Convex.NormalCone

/-!
# Normal-cone monotonicity infrastructure

This source-facing module records the canonical monotonicity theorem for a
normal-cone graph.
-/

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.7 (Monotonicity of the normal cone): the normal-cone graph of
every set in a continuous dual pair is monotone. -/
#check (DualPairing.isMonotone_normalConeGraph :
  ∀ (P : DualPairing X Xstar) (C : Set X), P.IsMonotone (P.normalConeGraph C))
