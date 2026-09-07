/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone

/-!
# Monotone-polar infrastructure

This source-facing module records the canonical monotone-polar definition and
membership API.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.2 (Monotone polar of a graph): the points monotonically related to
every point of `S` with respect to the quadratic form of `P`. -/
#check (DualPairing.monotonePolar :
  DualPairing X Xstar → Set (X × Xstar) → Set (X × Xstar))

#check (DualPairing.mem_monotonePolar :
  ∀ (P : DualPairing X Xstar) (S : Set (X × Xstar)) (z : X × Xstar),
    z ∈ P.monotonePolar S ↔ ∀ s ∈ S, 0 ≤ P.quadratic (z - s))

#check (DualPairing.monotonePolar_antitone :
  ∀ P : DualPairing X Xstar, Antitone P.monotonePolar)

end DualPairing
