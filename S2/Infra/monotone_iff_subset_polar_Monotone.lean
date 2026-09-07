/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone

/-!
# Monotonicity under subsets

This module exposes the monotonicity predicate for a dual pairing and its
restriction to subsets.
-/

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

#check (DualPairing.IsMonotone :
  DualPairing X Xstar → Set (X × Xstar) → Prop)

#check (DualPairing.IsMonotone.mono :
  ∀ (P : DualPairing X Xstar) {S T : Set (X × Xstar)},
    T ⊆ S → P.IsMonotone S → P.IsMonotone T)
