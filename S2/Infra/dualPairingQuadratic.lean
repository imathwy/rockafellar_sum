/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.DualPairing

/-!
# Quadratic pairing infrastructure

This source-facing module records the canonical quadratic-form API for a
continuous dual pairing.
-/

public section

universe u v

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/- Infrastructure D.1 (Quadratic pairing on a Banach-dual product) (1) -/
#check (DualPairing.quadratic : DualPairing X Xstar → QuadraticForm ℝ (X × Xstar))
#check (DualPairing.quadratic_apply :
  ∀ (P : DualPairing X Xstar) (x : X) (xstar : Xstar),
    P.quadratic (x, xstar) = P.toDual xstar x)

/- Infrastructure D.1 (Quadratic pairing on a Banach-dual product) (2) -/
#check (DualPairing.symmetric :
  DualPairing X Xstar → LinearMap.BilinForm ℝ (X × Xstar))
#check (DualPairing.symmetric_apply :
  ∀ (P : DualPairing X Xstar) (x y : X) (xstar ystar : Xstar),
    P.symmetric (x, xstar) (y, ystar) = P.toDual ystar x + P.toDual xstar y)
