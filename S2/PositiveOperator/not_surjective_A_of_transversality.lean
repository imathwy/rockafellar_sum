/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.ProperRange

/-!
# Proper range of `positiveOperator`

This module exposes the transpose-transversality proof that the positive
operator is not surjective.
-/

/- Lemma 3.8b (Transpose-surjectivity contradicts A* transversality):
`L1Seq.positiveOperator` is not surjective. -/
#check (L1Seq.positiveOperator_not_surjective :
  ¬ Function.Surjective L1Seq.positiveOperator)
