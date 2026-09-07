/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.PositiveDefinite

/-!
# Positive-operator equivalence

This module packages the hypothetical surjective positive operator as a
continuous-linear equivalence and exposes its inverse API.
-/

namespace L1Seq

/-- A surjective rational-time positive operator determines a continuous
real-linear equivalence from `L1Seq` to `C0Seq`. -/
public noncomputable def positiveOperatorEquivOfSurjective
    (h_surjective : Function.Surjective positiveOperator) : L1Seq ≃L[ℝ] C0Seq :=
  ContinuousLinearEquiv.ofBijective positiveOperator
    (LinearMap.ker_eq_bot.mpr positiveOperator_injective)
    (LinearMap.range_eq_top.mpr h_surjective)

/-- The forward continuous linear map of `positiveOperatorEquivOfSurjective` is
the rational-time positive operator. -/
public theorem positiveOperatorEquivOfSurjective_toContinuousLinearMap
    (h_surjective : Function.Surjective positiveOperator) :
    (positiveOperatorEquivOfSurjective h_surjective).toContinuousLinearMap =
      positiveOperator := by
  -- Unfold the project wrapper and use the constructor's forward-map computation rule.
  simpa only [positiveOperatorEquivOfSurjective] using
    (ContinuousLinearEquiv.coe_ofBijective positiveOperator
      (LinearMap.ker_eq_bot.mpr positiveOperator_injective)
      (LinearMap.range_eq_top.mpr h_surjective))

end L1Seq
