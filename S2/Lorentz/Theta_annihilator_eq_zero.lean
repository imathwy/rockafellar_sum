/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator.Elimination

/-!
# Triviality of the joint-coordinate annihilator

This module exposes elimination of all three coordinates from an annihilator
of the joint-coordinate map.
-/

public section

namespace L1Seq

/- Lemma 4.8c (Elimination of the scalar and c₀-dual components): substituting
`y = (-2 : ℝ) • intervalCoordinateOperator b` into the annihilator equation gives
`positiveOperator b = lam • d`; since `d ∉ Set.range positiveOperator`, all three
coordinates vanish. -/
#check (L1Seq.jointCoordinateMap_annihilator_eq_zero :
  (d : C0Seq) → d ∉ Set.range positiveOperator →
  (b : L1Seq) → (y : UnitL2) → (lam : ℝ) →
  positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y +
    lam • C0Seq.pairingL d = 0 →
  (b, y, lam) = (0, 0, 0))

end L1Seq
