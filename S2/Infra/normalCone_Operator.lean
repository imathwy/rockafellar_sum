/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Convex.NormalCone

/-!
# Normal-cone operator bridge

This source-facing module records the canonical normal-cone operator and its
basic graph bridge.
-/

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]
variable (P : DualPairing X Xstar) (C : Set X) (x : X) (xstar : Xstar)

#check (DualPairing.normalCone :
  DualPairing X Xstar → Set X → SetValuedOperator X Xstar)
#check (DualPairing.mem_normalCone P C x xstar :
  xstar ∈ P.normalCone C x ↔
    x ∈ C ∧ ∀ y ∈ C, P.toLinearPairing (y - x) xstar ≤ 0)
#check (DualPairing.normalConeGraph : DualPairing X Xstar → Set X → SetRel X Xstar)
#check (DualPairing.mem_graph_normalCone P C x xstar :
  (x, xstar) ∈ P.normalConeGraph C ↔
    x ∈ C ∧ ∀ y ∈ C, P.toLinearPairing (y - x) xstar ≤ 0)
#check (DualPairing.normalConeDom : DualPairing X Xstar → Set X → Set X)
#check (DualPairing.dom_normalCone P C : P.normalConeDom C = C)
#check (DualPairing.mem_dom_normalCone P C x : x ∈ P.normalConeDom C ↔ x ∈ C)
