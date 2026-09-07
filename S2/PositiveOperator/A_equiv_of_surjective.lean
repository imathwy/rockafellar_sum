/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Equiv

/-!
# Equivalence Under Surjectivity

This module records the continuous-linear equivalence forced by surjectivity.
-/

/- Lemma 3.8a (Surjectivity would make A a continuous linear equivalence) -/
#check (L1Seq.positiveOperatorEquivOfSurjective :
  Function.Surjective L1Seq.positiveOperator → L1Seq ≃L[ℝ] C0Seq)

#check (L1Seq.positiveOperatorEquivOfSurjective_toContinuousLinearMap :
  ∀ h_surjective : Function.Surjective L1Seq.positiveOperator,
    (L1Seq.positiveOperatorEquivOfSurjective h_surjective).toContinuousLinearMap =
      L1Seq.positiveOperator)
