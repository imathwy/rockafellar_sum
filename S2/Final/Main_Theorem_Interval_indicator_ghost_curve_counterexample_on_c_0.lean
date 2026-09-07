module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.Counterexample

public section

open scoped Pointwise

/- Main Theorem (Interval-indicator ghost-curve counterexample on $c_0$) -/
#check (Lorentz.exists_ghostCurveCounterexample :
    ∃ M : SetValuedOperator C0Seq L1Seq,
      (Maximal C0Seq.coordinateDualPairing.IsMonotone M.graph ∧
        Maximal C0Seq.coordinateDualPairing.IsMonotone
          (C0Seq.coordinateDualPairing.normalConeGraph C0Seq.finalConstraint)) ∧
      (Set.Nonempty
          (M.dom ∩ interior
            (C0Seq.coordinateDualPairing.normalConeDom C0Seq.finalConstraint)) ∧
        ¬ Maximal C0Seq.coordinateDualPairing.IsMonotone
          (M + C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph ∧
        (0, 0) ∈ C0Seq.monotonePolar
            (M + C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph \
          (M + C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph))
