/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator.Triviality

/-!
# Trivial continuous annihilator

This module records that the continuous annihilator of the joint-coordinate
range is trivial outside the positive-operator range.
-/

public section

/- Lemma 4.9a (The continuous annihilator of range Θ is trivial): every
continuous functional on `C0Seq × (UnitL2 × ℝ)` that vanishes on the range of
`jointCoordinateMap d` is zero when `d` lies outside the range of
`positiveOperator`. -/
#check (L1Seq.jointCoordinateMap_annihilator_eq_bot :
  (d : C0Seq) → d ∉ Set.range L1Seq.positiveOperator →
    StrongDual.polarSubmodule ℝ (L1Seq.jointCoordinateMap d).range = ⊥)
