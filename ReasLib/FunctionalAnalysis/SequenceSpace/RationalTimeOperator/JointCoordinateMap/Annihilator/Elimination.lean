module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.PositiveDefinite
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint.C0Range

public section

namespace L1Seq

/-- The joint-coordinate annihilator equation and the symmetric-part identity give the
balance between the interval-coordinate adjoint and the canonical `C0Seq` pairing. -/
theorem jointCoordinateMap_annihilator_balance
    (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ)
    (h_equation : positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y +
      lam • C0Seq.pairingL d = 0) :
    intervalCoordinateAdjoint ((2 : ℝ) • intervalCoordinateOperator b + y) =
      C0Seq.pairingL (positiveOperator b - lam • d) := by
  -- Evaluate the symmetric-part identity at `b`, and separately isolate the
  -- transpose-adjoint sum supplied by the annihilator equation.
  have h_sym := positiveOperator_symmetricPart
  have h_sym_b := congrArg (fun f : L1Seq →L[ℝ] StrongDual ℝ L1Seq => f b) h_sym
  have h_transpose :
      positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y =
        -(lam • C0Seq.pairingL d) := by
    exact eq_neg_of_add_eq_zero_left h_equation
  simp only [map_add, two_smul]
  have h_sym_b' :
      C0Seq.pairingL (positiveOperator b) + positiveOperator.reindexedTranspose b =
        intervalCoordinateAdjoint (intervalCoordinateOperator b) +
          intervalCoordinateAdjoint (intervalCoordinateOperator b) := by
    simpa [ContinuousLinearMap.comp_apply, two_nsmul] using h_sym_b
  -- Substitute those two identities after linearity has exposed the three summands.
  calc
    intervalCoordinateAdjoint (intervalCoordinateOperator b) +
        intervalCoordinateAdjoint (intervalCoordinateOperator b) +
        intervalCoordinateAdjoint y =
        (C0Seq.pairingL (positiveOperator b) +
          positiveOperator.reindexedTranspose b) + intervalCoordinateAdjoint y := by
            exact congrArg (fun q : StrongDual ℝ L1Seq => q + intervalCoordinateAdjoint y)
              h_sym_b'.symm
    _ = C0Seq.pairingL (positiveOperator b - lam • d) := by
      rw [add_assoc, h_transpose]
      simp [map_sub, map_smul]
      abel

/-- Transversality of the interval-coordinate adjoint eliminates the Hilbert component of
a joint-coordinate annihilator. -/
theorem jointCoordinateMap_annihilator_y
    (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ)
    (h_equation : positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y +
      lam • C0Seq.pairingL d = 0) :
    y = (-2 : ℝ) • intervalCoordinateOperator b := by
  -- The balance equation exhibits the combined Hilbert component's adjoint in
  -- the canonical `C0Seq` range.
  have h_balance := jointCoordinateMap_annihilator_balance d b y lam h_equation
  have h_adjoint :
      intervalCoordinateAdjoint ((2 : ℝ) • intervalCoordinateOperator b + y) ∈
        Set.range C0Seq.pairingL := by
    refine ⟨positiveOperator b - lam • d, ?_⟩
    exact h_balance.symm
  -- Transversality kills the combined component; additive rearrangement isolates `y`.
  have h_zero : (2 : ℝ) • intervalCoordinateOperator b + y = 0 :=
    intervalCoordinateAdjoint_transverse _ h_adjoint
  have h_neg : y = -((2 : ℝ) • intervalCoordinateOperator b) := by
    have h_zero' : y + (2 : ℝ) • intervalCoordinateOperator b = 0 := by
      simpa [add_comm] using h_zero
    exact eq_neg_of_add_eq_zero_left h_zero'
  simpa [neg_smul] using h_neg

/-- Membership in the polar of a joint-coordinate range determines the Hilbert component
of the representing product functional. -/
theorem jointCoordinateMap_annihilator_y_of_mem
    (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ)
    (h_annihilates :
      ContinuousLinearMap.dualProdMap
          (C0Seq.dualEquivL1.symm b, (InnerProductSpace.toDual ℝ UnitL2) y, lam) ∈
        StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range) :
    y = (-2 : ℝ) • intervalCoordinateOperator b := by
  -- Translate polar membership to the equation-level elimination result.
  apply jointCoordinateMap_annihilator_y d b y lam
  exact (jointCoordinateMap_annihilator_iff d b y lam).1 h_annihilates

/-- Membership in the polar of a joint-coordinate range identifies the positive-operator
coordinate with the prescribed scalar multiple. -/
theorem jointCoordinateMap_annihilator_positiveOperator_of_mem
    (d : C0Seq) (b : L1Seq) (y : UnitL2) (lam : ℝ)
    (h_annihilates :
      ContinuousLinearMap.dualProdMap
          (C0Seq.dualEquivL1.symm b, (InnerProductSpace.toDual ℝ UnitL2) y, lam) ∈
        StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range) :
    positiveOperator b = lam • d := by
  -- Recover both the annihilator equation and its eliminated Hilbert coordinate.
  have h_equation :=
    (jointCoordinateMap_annihilator_iff d b y lam).1 h_annihilates
  have h_y := jointCoordinateMap_annihilator_y_of_mem d b y lam h_annihilates
  have h_balance := jointCoordinateMap_annihilator_balance d b y lam h_equation
  -- The Hilbert-coordinate formula makes the adjoint side of the balance vanish.
  have h_pair : C0Seq.pairingL (positiveOperator b - lam • d) = 0 := by
    rw [← h_balance, h_y]
    simp
  have h_pair_eq :
      C0Seq.pairingL (positiveOperator b - lam • d) = C0Seq.pairingL 0 := by
    simpa using h_pair
  have h_diff : positiveOperator b - lam • d = 0 :=
    C0Seq.pairingL_injective h_pair_eq
  -- Injectivity of the canonical pairing reduces the claim to subtraction by zero.
  exact sub_eq_zero.mp h_diff

/-- If a vector lies outside the range of the positive operator, its joint-coordinate
annihilator equation forces all three coordinates to vanish. -/
theorem jointCoordinateMap_annihilator_eq_zero
    (d : C0Seq) (h_missing : d ∉ Set.range positiveOperator)
    (b : L1Seq) (y : UnitL2) (lam : ℝ)
    (h_equation : positiveOperator.reindexedTranspose b + intervalCoordinateAdjoint y +
      lam • C0Seq.pairingL d = 0) :
    (b, y, lam) = (0, 0, 0) := by
  -- Translate the displayed equation to polar membership and use the established
  -- elimination identity to expose the positive-operator coordinate.
  have h_annihilates :
      ContinuousLinearMap.dualProdMap
          (C0Seq.dualEquivL1.symm b, (InnerProductSpace.toDual ℝ UnitL2) y, lam) ∈
        StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range :=
    (jointCoordinateMap_annihilator_iff d b y lam).2 h_equation
  have h_pos :=
    jointCoordinateMap_annihilator_positiveOperator_of_mem d b y lam h_annihilates
  -- A nonzero scalar would make `d` the image of the rescaled vector `lam⁻¹ • b`.
  have h_lam : lam = 0 := by
    by_contra h_lam
    apply h_missing
    refine ⟨lam⁻¹ • b, ?_⟩
    calc
      positiveOperator (lam⁻¹ • b) = lam⁻¹ • positiveOperator b := by
        exact map_smul positiveOperator (lam⁻¹) b
      _ = lam⁻¹ • (lam • d) := by rw [h_pos]
      _ = d := by simp [h_lam]
  -- With the scalar gone, injectivity removes `b`; the Hilbert-coordinate formula
  -- then removes `y`.
  have h_b_zero : b = 0 := by
    apply positiveOperator_injective
    simpa [h_lam] using h_pos
  have h_y := jointCoordinateMap_annihilator_y d b y lam h_equation
  have h_y_zero : y = 0 := by
    simpa [h_b_zero] using h_y
  -- Assemble the three coordinate equalities in the nested product.
  simp [h_b_zero, h_y_zero, h_lam]

end L1Seq
