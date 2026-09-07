/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart

/-!
# The symmetric part of the positive operator

This module exposes the operator-valued identity for the pairing, transpose, and adjoint.
-/

/- Lemma 3.5b (Operator-valued symmetric-part identity) -/
#check (L1Seq.positiveOperator_symmetricPart :
  C0Seq.pairingL.comp L1Seq.positiveOperator + L1Seq.positiveOperator.reindexedTranspose =
    2 • (L1Seq.intervalCoordinateAdjoint.comp L1Seq.intervalCoordinateOperator))
