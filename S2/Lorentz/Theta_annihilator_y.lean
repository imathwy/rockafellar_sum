/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator.Elimination

/-!
# Hilbert-component annihilator elimination

This module exposes the balance and Hilbert-component consequences of the
joint-coordinate annihilator equation.
-/

public section

namespace L1Seq

/- The annihilator equation and the symmetric-part identity give the balance between the
interval-coordinate adjoint and the canonical `C0Seq` pairing. -/
#check (jointCoordinateMap_annihilator_balance :
  ∀ (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ),
    positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y +
        lam • C0Seq.pairingL d = 0 →
      intervalCoordinateAdjoint ((2 : ℝ) • intervalCoordinateOperator b + y) =
        C0Seq.pairingL (positiveOperator b - lam • d))

/- Lemma 4.8b (Elimination of the Hilbert component of an annihilator): the typed
annihilator equation determines the Hilbert component. -/
#check (jointCoordinateMap_annihilator_y :
  ∀ (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ),
    positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y +
        lam • C0Seq.pairingL d = 0 →
      y = (-2 : ℝ) • intervalCoordinateOperator b)

end L1Seq
