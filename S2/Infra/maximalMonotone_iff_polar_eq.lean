/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone

/-!
# Maximal monotonicity and the polar

This source-facing module records the canonical polar equality criterion for
maximal monotonicity.
-/

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.4 (Maximal monotonicity as equality with the polar): a monotone
graph is maximal among monotone graphs exactly when it equals its monotone polar. -/
#check (DualPairing.maximalMonotone_iff_polar_eq :
  ∀ (P : DualPairing X Xstar) (S : Set (X × Xstar)), P.IsMonotone S →
    (Maximal (P.IsMonotone) S ↔ P.monotonePolar S = S))
