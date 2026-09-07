module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap
public import ReasLib.FunctionalAnalysis.SequenceSpace.L1.Annihilator
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Transpose
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint

public section

namespace L1Seq

/-- `L1Seq.jointCoordinateMap_annihilator_iff`: a product functional annihilates the range
of the joint coordinate map exactly when the sum of its three typed transpose coordinates
is zero. -/
theorem jointCoordinateMap_annihilator_iff
    (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ) :
    ContinuousLinearMap.dualProdMap
        ((C0Seq.dualEquivL1).symm b, (InnerProductSpace.toDual ℝ UnitL2) y, lam) ∈
        StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range ↔
        positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y +
          lam • C0Seq.pairingL d = 0 := by
  -- Apply the generic product-range criterion through the joint map's coordinate specification.
  have h_prod := ContinuousLinearMap.annihilates_prodRange_iff
    (T := jointCoordinateMap d)
    (T₁ := positiveOperator)
    (T₂ := intervalCoordinateOperator)
    (T₃ := C0Seq.pairingL d)
    (b := C0Seq.dualEquivL1.symm b)
    (y := (InnerProductSpace.toDual ℝ UnitL2) y)
    (lam := lam)
    (jointCoordinateMap_apply d)
  -- Identify the second paper transpose with the interval-coordinate adjoint pointwise.
  have h_interval :
      intervalCoordinateOperator.paperTranspose ((InnerProductSpace.toDual ℝ UnitL2) y) =
        intervalCoordinateAdjoint y := by
    ext a
    simpa only [ContinuousLinearMap.paperTranspose_apply,
      InnerProductSpace.toDual_apply_apply] using
      (intervalCoordinateAdjoint_apply y a).symm
  -- Reindex the first paper transpose through the canonical duality of `C0Seq`.
  have h_transpose :
      positiveOperator.paperTranspose (C0Seq.dualEquivL1.symm b) =
        positiveOperator.reindexedTranspose b := by
    exact (ContinuousLinearMap.reindexedTranspose_apply positiveOperator b).symm
  -- Rewrite the invariant supplied by the generic criterion into the target notation.
  rw [h_transpose, h_interval] at h_prod
  exact h_prod

end L1Seq
