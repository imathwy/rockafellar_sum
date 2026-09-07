/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.PositiveDefinite

/-!
# Strict Positivity and Injectivity

This module exposes the quadratic identity, strict positivity, and injectivity of `A`.
-/

/- The quadratic identity identifies the pairing with the squared norm of the
interval-coordinate image. -/
#check (L1Seq.positiveOperator_quadratic_eq_norm_sq :
  ∀ a : L1Seq,
    C0Seq.pairingL (L1Seq.positiveOperator a) a =
      ‖L1Seq.intervalCoordinateOperator a‖ ^ 2)

/- Corollary 3.4 (Strict positivity and injectivity of $A$) (1): for every
nonzero `a`, the quadratic pairing of `positiveOperator a` with `a` is strictly
positive. -/
#check (L1Seq.positiveOperator_quadratic_pos :
  ∀ a : L1Seq, a ≠ 0 → 0 < C0Seq.pairingL (L1Seq.positiveOperator a) a)

/- Corollary 3.4 (Strict positivity and injectivity of $A$) (2): the positive
operator is injective. -/
#check (L1Seq.positiveOperator_injective :
  Function.Injective L1Seq.positiveOperator)
