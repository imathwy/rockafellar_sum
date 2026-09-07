/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.QuadraticIdentity

/-!
# Quadratic identity for the positive operator

This module relates the quadratic pairing to the Gram sum and interval-coordinate norm.
-/

#check (L1Seq.positiveOperator_quadratic_eq_gramTsum :
  ∀ a : L1Seq,
    C0Seq.pairingL (L1Seq.positiveOperator a) a =
      ∑' p : ℕ × ℕ,
        min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2)

/- Lemma 3.3 (Quadratic identity for $A$) -/
#check (L1Seq.positiveOperator_quadratic_eq_norm_sq :
  ∀ a : L1Seq,
    C0Seq.pairingL (L1Seq.positiveOperator a) a =
      ‖L1Seq.intervalCoordinateOperator a‖ ^ 2)
