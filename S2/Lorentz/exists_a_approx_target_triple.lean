module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.DenseRange

public section

/-
Lemma 4.10a (Approximation of the prescribed triple by Θ): one sequence simultaneously
approximates the prescribed positive, interval, and pairing coordinates.
-/
#check (L1Seq.exists_a_approx_target_triple :
  ∀ (d : C0Seq), d ∉ Set.range L1Seq.positiveOperator →
    ∀ (p : ℝ) (x₀ : C0Seq) (v : UnitL2) (r ε : ℝ), 0 < ε →
      ∃ a : L1Seq,
        ‖L1Seq.positiveOperator a - ((p + r) • d - x₀)‖ < ε ∧
        ‖L1Seq.intervalCoordinateOperator a - v‖ < ε ∧
        ‖C0Seq.pairingL d a - (p - r)‖ < ε)
