/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Jump

/-!
# Isolated jumps recover coefficients

This module relates isolated representative jumps to one coefficient and its tail remainder.
-/

noncomputable section

/- Lemma 2.7d (Isolated jump recovers one coefficient) (1): isolating the
breakpoint indexed by `n₀` decomposes the representative jump into `a n₀` and
the contribution from indices outside `J`. -/
#check (L1Seq.pointwiseRepresentative_sub_eq_apply_add_jumpRemainder :
  ∀ (a : L1Seq) (n₀ : ℕ) (J : Finset ℕ) (sLeft sRight : ℝ), n₀ ∈ J →
    sLeft ∈ Set.Ioo (0 : ℝ) (rationalTime n₀) →
    sRight ∈ Set.Ioo (rationalTime n₀) 1 →
    (∀ n ∈ J, n ≠ n₀ → rationalTime n ∉ Set.Ioc sLeft sRight) →
    L1Seq.pointwiseRepresentative a sLeft - L1Seq.pointwiseRepresentative a sRight =
      a n₀ + L1Seq.jumpRemainder a J sLeft sRight)

/- Lemma 2.7d (Isolated jump recovers one coefficient) (2): the contribution
to the jump from indices outside `J` is controlled by their absolute tail. -/
#check (L1Seq.abs_jumpRemainder_lt :
  ∀ (a : L1Seq) (J : Finset ℕ) (sLeft sRight ε : ℝ),
    (∑' n : {n // n ∉ J}, |a n|) < ε →
      |L1Seq.jumpRemainder a J sLeft sRight| < ε)

/- Lemma 2.7d (Isolated jump recovers one coefficient) (3): if the
representative vanishes at both endpoints, the isolated coefficient is smaller
than the prescribed tail bound. -/
#check (L1Seq.abs_apply_lt_of_pointwiseRepresentative_eq_zero :
  ∀ (a : L1Seq) (n₀ : ℕ) (J : Finset ℕ) (sLeft sRight ε : ℝ), n₀ ∈ J →
    sLeft ∈ Set.Ioo (0 : ℝ) (rationalTime n₀) →
    sRight ∈ Set.Ioo (rationalTime n₀) 1 →
    (∀ n ∈ J, n ≠ n₀ → rationalTime n ∉ Set.Ioc sLeft sRight) →
    (∑' n : {n // n ∉ J}, |a n|) < ε →
    L1Seq.pointwiseRepresentative a sLeft = 0 →
    L1Seq.pointwiseRepresentative a sRight = 0 →
      |a n₀| < ε)
