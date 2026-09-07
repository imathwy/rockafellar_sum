module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator.Triviality

public section

/- Lemma 4.9a (The continuous annihilator of range Θ is trivial): every
continuous functional on `C0Seq × (UnitL2 × ℝ)` that vanishes on the range of
`jointCoordinateMap d` is zero when `d` lies outside the range of
`positiveOperator`. -/
#check (L1Seq.jointCoordinateMap_annihilator_eq_bot :
  (d : C0Seq) → d ∉ Set.range L1Seq.positiveOperator →
    StrongDual.polarSubmodule ℝ (L1Seq.jointCoordinateMap d).range = ⊥)
