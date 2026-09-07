module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Adjoint
public import ReasLib.MeasureTheory.UnitL2.Primitive
public import ReasLib.MeasureTheory.UnitL2.Primitive.Holder
public import ReasLib.MeasureTheory.UnitL2.RationalIntervalIndicator.Integral
public import ReasLib.Topology.RationalTime

public section

open Topology
open scoped InnerProductSpace

namespace UnitL2

/-- If the interval-coordinate adjoint of a vector lies in the canonical image of
`C0Seq`, then its primitive at the rational sample times tends to zero. -/
theorem primitive_rationalTime_tendsto_zero (y : UnitL2)
    (h_adjoint : L1Seq.intervalCoordinateAdjoint y ∈ Set.range C0Seq.pairingL) :
    Filter.Tendsto (fun n : ℕ ↦ primitive y (rationalTime n)) Filter.atTop (𝓝 0) := by
  -- Choose the null sequence whose pairing functional is the given adjoint.
  obtain ⟨x, hx⟩ := h_adjoint
  -- Identify every primitive sample with the corresponding coordinate of that sequence.
  have h_sample : ∀ n : ℕ, primitive y (rationalTime n) = x n := by
    intro n
    have h_eval :=
      congrArg (fun f : StrongDual ℝ L1Seq ↦ f (lp.single 1 n (1 : ℝ))) hx
    have h_pair : C0Seq.pairingL x (lp.single 1 n (1 : ℝ)) = x n := by
      -- The coordinate pairing collapses to the unique support point of the singleton.
      rw [C0Seq.pairingL_apply]
      rw [tsum_eq_single n]
      · rw [lp.single_apply_self, mul_one]
      · intro m hm
        simp only [lp.single_apply, Pi.single_apply, if_neg hm, mul_zero]
    -- The adjoint formula and the interval-indicator integral formula provide the bridge.
    rw [L1Seq.intervalCoordinateAdjoint_apply_single] at h_eval
    have h_inner : ⟪y, UnitL2.rationalIntervalVec n⟫_ℝ = x n := by
      rw [← h_pair]
      exact h_eval.symm
    rw [inner_rationalIntervalVec_eq_integral] at h_inner
    simpa only [primitive_apply] using h_inner
  have h_samples :
      (fun n : ℕ ↦ primitive y (rationalTime n)) = fun n : ℕ ↦ x n := by
    funext n
    exact h_sample n
  -- Transport the defining convergence of `C0Seq` across the sample identity.
  rw [h_samples]
  exact C0Seq.tendsto_zero x

end UnitL2

namespace L1Seq

/-- A vector in `UnitL2` vanishes if its interval-coordinate adjoint lies in the
canonical image of `C0Seq`. -/
theorem intervalCoordinateAdjoint_transverse (y : UnitL2)
    (h_adjoint : intervalCoordinateAdjoint y ∈ Set.range C0Seq.pairingL) : y = 0 := by
  -- Convert the range hypothesis into convergence of the primitive samples.
  have h_samples := UnitL2.primitive_rationalTime_tendsto_zero y h_adjoint
  -- Continuity and tail-density extend the sampled zeros across the unit interval.
  have h_primitive : ∀ t ∈ Set.Icc (0 : ℝ) 1, UnitL2.primitive y t = 0 := by
    apply continuousOn_eq_zero_of_tendsto_rationalTime
    · exact UnitL2.continuousOn_primitive y
    · exact h_samples
  -- Primitive uniqueness now identifies the original `UnitL2` vector with zero.
  apply UnitL2.eq_zero_of_primitive_eq_zero y
  intro t ht
  simpa only [UnitL2.primitive_apply] using h_primitive t ht

/-- The range of the interval-coordinate adjoint meets the canonical image of
`C0Seq` only at zero. -/
theorem range_intervalCoordinateAdjoint_inter_range_pairingL :
    Set.range intervalCoordinateAdjoint ∩ Set.range C0Seq.pairingL = {0} := by
  ext z
  constructor
  · intro hz
    -- A common range element has an adjoint preimage satisfying transversality.
    rcases hz.1 with ⟨y, rfl⟩
    rcases hz.2 with ⟨x, hx⟩
    have hy : y = 0 := intervalCoordinateAdjoint_transverse y ⟨x, hx⟩
    rw [Set.mem_singleton_iff, hy, map_zero]
  · intro hz
    -- Reduce the reverse inclusion to the zero images of the two linear maps.
    have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
    subst z
    have h_zero_adjoint : intervalCoordinateAdjoint (0 : UnitL2) = 0 :=
      map_zero intervalCoordinateAdjoint
    have h_zero_pairing : C0Seq.pairingL (0 : C0Seq) = 0 :=
      map_zero C0Seq.pairingL
    constructor
    · exact ⟨0, h_zero_adjoint⟩
    · exact ⟨0, h_zero_pairing⟩

end L1Seq
