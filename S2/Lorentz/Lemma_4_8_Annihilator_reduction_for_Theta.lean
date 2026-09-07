module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator.Elimination

public section

namespace L1Seq

/- Lemma 4.8 (Annihilator reduction for $\Theta$) (1)
A functional represented by `(b, y, lam)` that annihilates the range of
`jointCoordinateMap d` has Hilbert component
`y = (-2 : ℝ) • intervalCoordinateOperator b`.
-/
#check (L1Seq.jointCoordinateMap_annihilator_y_of_mem :
  ∀ (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ),
    ContinuousLinearMap.dualProdMap
          (C0Seq.dualEquivL1.symm b, (InnerProductSpace.toDual ℝ UnitL2) y, lam) ∈
        StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range →
      y = (-2 : ℝ) • intervalCoordinateOperator b)

/- Lemma 4.8 (Annihilator reduction for $\Theta$) (2)
A functional represented by `(b, y, lam)` that annihilates the range of
`jointCoordinateMap d` satisfies `positiveOperator b = lam • d`.
-/
#check (L1Seq.jointCoordinateMap_annihilator_positiveOperator_of_mem :
  ∀ (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ),
      ContinuousLinearMap.dualProdMap
          (C0Seq.dualEquivL1.symm b, (InnerProductSpace.toDual ℝ UnitL2) y, lam) ∈
        StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range →
      positiveOperator b = lam • d)

end L1Seq
