/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive

/-!
# A future-ray base vector

This module records a parametrized base vector with controlled Lorentz coordinates.
-/

/- Lemma 6.16 (A future-ray base vector): a single vector in
`Lorentz.parametrizedSubspace d` has positive coordinate `1`, negative-coordinate
norm less than `1 / 16`, and first ambient-coordinate norm less than `1 / 8`. -/
#check (Lorentz.exists_futureRayBase :
  ∀ (d : C0Seq) (hd : d ≠ 0),
    d ∉ Set.range L1Seq.positiveOperator →
      ∃ v : Lorentz.parametrizedSubspace d,
        Lorentz.positiveCoordinate d hd v = 1 ∧
        ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 ∧
        ‖(v : C0Seq × L1Seq).1‖ < (1 : ℝ) / 8)
