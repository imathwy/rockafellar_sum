/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import S2.PositiveOperator.J_comp_A_add_Astar

/-!
# Polarization of the symmetric part

This module records the operator representation of the symmetric part of the positive operator.
-/

/- Lemma 3.5 (Polarization identity for the symmetric part of $A$):
`C0Seq.pairingL`, `ContinuousLinearMap.reindexedTranspose`, and
`L1Seq.intervalCoordinateAdjoint` represent `J`, `A*`, and `V*`, respectively. -/
#check L1Seq.positiveOperator_symmetricPart
