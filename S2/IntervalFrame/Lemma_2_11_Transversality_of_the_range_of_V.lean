/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint.C0Range

/-!
# Transversality of the range of `V*`

This source-facing module records the canonical adjoint transversality
criterion.
-/

public section

/- Lemma 2.11 (Transversality of the range of $V^*$): if the adjoint image of
`y : UnitL2` lies in the canonical image of `C0Seq`, then `y = 0`. -/
#check (L1Seq.intervalCoordinateAdjoint_transverse :
  ∀ (y : UnitL2), L1Seq.intervalCoordinateAdjoint y ∈ Set.range C0Seq.pairingL → y = 0)

#check (L1Seq.range_intervalCoordinateAdjoint_inter_range_pairingL :
  Set.range L1Seq.intervalCoordinateAdjoint ∩ Set.range C0Seq.pairingL = {0})
