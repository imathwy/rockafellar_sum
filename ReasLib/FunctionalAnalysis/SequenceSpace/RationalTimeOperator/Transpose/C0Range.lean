module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint.C0Range
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Injective

namespace L1Seq

/-- If the reindexed transpose of the rational-time positive operator maps a summable
sequence into the canonical image of `C0Seq`, then that sequence vanishes. -/
public theorem positiveOperator_reindexedTranspose_transverse (b : L1Seq)
    (h_transpose : positiveOperator.reindexedTranspose b ∈ Set.range C0Seq.pairingL) :
    b = 0 := by
  -- The symmetric-part identity first puts twice the relevant adjoint in the canonical range.
  have h_two := two_smul_intervalCoordinateAdjoint_mem_range b h_transpose
  rcases h_two with ⟨x, hx⟩
  -- Scaling its witness by one half preserves range membership and removes the factor two.
  have h_adjoint : intervalCoordinateAdjoint (intervalCoordinateOperator b) ∈
      Set.range C0Seq.pairingL := by
    refine ⟨(1 / 2 : ℝ) • x, ?_⟩
    rw [map_smul]
    have hx' : C0Seq.pairingL x =
        intervalCoordinateAdjoint (intervalCoordinateOperator b) +
          intervalCoordinateAdjoint (intervalCoordinateOperator b) := by
      simpa only [two_nsmul] using hx
    rw [hx']
    rw [smul_add]
    module
  -- Adjoint transversality kills the interval-coordinate image of `b`.
  have h_zero : intervalCoordinateOperator b = 0 :=
    intervalCoordinateAdjoint_transverse _ h_adjoint
  have h_zero_operator : intervalCoordinateOperator (0 : L1Seq) = 0 :=
    map_zero intervalCoordinateOperator
  have h_equal_images : intervalCoordinateOperator b = intervalCoordinateOperator 0 :=
    h_zero.trans h_zero_operator.symm
  -- Injectivity of the interval-coordinate operator then recovers `b = 0`.
  exact intervalCoordinateOperator_injective h_equal_images

/-- The range of the reindexed transpose of the rational-time positive operator meets
the canonical image of `C0Seq` only at zero. -/
public theorem range_positiveOperator_reindexedTranspose_inter_range_pairingL :
    Set.range positiveOperator.reindexedTranspose ∩ Set.range C0Seq.pairingL = {0} := by
  ext z
  constructor
  · intro hz
    -- A common range element has a transpose preimage satisfying the pointwise theorem.
    rcases hz.1 with ⟨b, rfl⟩
    rcases hz.2 with ⟨x, hx⟩
    have hb : b = 0 := positiveOperator_reindexedTranspose_transverse b ⟨x, hx⟩
    rw [Set.mem_singleton_iff, hb, map_zero]
  · intro hz
    -- Conversely, zero is the image of zero under both continuous linear maps.
    have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
    subst z
    have h_zero_transpose : positiveOperator.reindexedTranspose (0 : L1Seq) = 0 :=
      map_zero positiveOperator.reindexedTranspose
    have h_zero_pairing : C0Seq.pairingL (0 : C0Seq) = 0 :=
      map_zero C0Seq.pairingL
    constructor
    · exact ⟨0, h_zero_transpose⟩
    · exact ⟨0, h_zero_pairing⟩

end L1Seq
