/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.NormalCone.ClosedBall
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.ProperRange
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteTimeZero
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftAnchor
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorCoordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Maximal
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.ConstraintQualification
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.NormalCone
public import ReasLib.Analysis.C0Seq.NormalCone.Origin
import ReasLib.Analysis.Normed.Operator.Range

/-!
# Interval-indicator ghost-curve counterexample

This module assembles the normalized missing-range direction, ghost-curve
operator, fixed closed-ball normal cone, and the final nonmaximal sum witness.
-/

public section

open scoped Pointwise

namespace Lorentz

/-- There is a maximally monotone operator on real `c₀` with real `ℓ¹` values
whose sum with the normal cone of the closed radius-`1 / 2` ball fails to be
maximally monotone, despite the interior constraint qualification. More
precisely, the origin lies in the monotone polar of the sum graph but not in
the graph itself. -/
theorem exists_ghostCurveCounterexample :
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
          (M + C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph) := by
  classical
  -- Match source equation (17) with a normalized vector outside the operator range.
  let d : C0Seq :=
    ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective
  have hd_spec : d ∉ Set.range L1Seq.positiveOperator ∧ ‖d‖ = (1 : ℝ) := by
    simpa [d] using
      (ContinuousLinearMap.unitVectorOutsideRange_spec
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
  obtain ⟨h_missing, hd_norm⟩ := hd_spec
  have hd : d ≠ 0 :=
    norm_ne_zero_iff.mp (hd_norm.symm ▸ one_ne_zero)
  let nbar : HilbertProd2 UnitL2 := HilbertProd2.mk 0 (1 / 64 : ℝ)
  have hnbar : ‖nbar‖ = (1 / 64 : ℝ) := by
    have hsq := HilbertProd2.norm_mk_sq (0 : UnitL2) (1 / 64 : ℝ)
    dsimp [nbar] at hsq ⊢
    have hn : 0 ≤ ‖HilbertProd2.mk (0 : UnitL2) (1 / 64 : ℝ)‖ := norm_nonneg _
    apply (sq_eq_sq₀ hn (by norm_num)).mp
    simpa using hsq
  obtain ⟨z₀, hPZero, hZero, hApprox⟩ :=
    exists_remoteTimeZero d hd h_missing nbar hnbar
  have hNZero : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ) :=
    (negativeCoordinate_norm_mem_Ioo d hd nbar hnbar z₀ hApprox).2
  have hqZero : C0Seq.quadraticPairing z₀ < 0 :=
    quadraticPairing_neg_of_timeZero_approx d hd nbar hnbar z₀ hPZero hApprox
  obtain ⟨zLeft, hPLeft, hLeft, hLeftApprox, hNLeft, hAnchor⟩ :=
    exists_leftAnchor d hd h_missing z₀ hNZero
  obtain ⟨v, hvP, hvN, hvX⟩ := exists_futureRayBase d hd h_missing
  let c : ∀ p q : ℕ, p < q → ℕ → L1Seq := fun p q hpq ↦
    Classical.choose (L1Seq.exists_remoteDetectorCopy d p q hpq)
  let h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d := fun p q hpq n ↦
    remoteDetectorPoint d p q (c p q hpq) n
  have hc : ∀ p q (hpq : p < q), ∀ n,
      Function.support (fun m ↦ c p q hpq n m) ⊆ Set.Ioi n ∧
        ‖c p q hpq n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c p q hpq n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ) := by
    intro p q hpq
    exact Classical.choose_spec (L1Seq.exists_remoteDetectorCopy d p q hpq)
  have h_positive : ∀ p q (hpq : p < q) n,
      positiveCoordinate d hd (h p q hpq n) = 0 := by
    intro p q hpq n
    dsimp [h]
    exact positiveCoordinate_remoteDetectorPoint d hd p q (c p q hpq) n
  have h_tendsto : ∀ p q (hpq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q hpq n))
        Filter.atTop (nhds 0) := by
    intro p q hpq
    dsimp [h]
    exact negativeCoordinate_remoteDetectorPoint_tendsto_zero d hd p q hpq
      (c p q hpq) (hc p q hpq)
  have h_pairing : ∀ (w : C0Seq × L1Seq) p q (hpq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q hpq n))
        Filter.atTop (nhds (detectorFunctional d p q w)) := by
    intro w p q hpq
    dsimp [h]
    exact remoteDetectorPoint_pairing_tendsto d w p q hpq (c p q hpq)
      (hc p q hpq)
  let M : SetValuedOperator C0Seq L1Seq :=
    ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v
  have hz₀_mem : (z₀ : C0Seq × L1Seq) ∈ M.graph := by
    dsimp [M]
    rw [graph_ghostCurveOperator]
    apply (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v z₀).2
    constructor
    · rw [hPZero]
      norm_num
    · rw [hPZero, ghostCurveN_zero]
  have hMmax : Maximal C0Seq.coordinateDualPairing.IsMonotone M.graph := by
    dsimp [M]
    exact maximalMonotone_ghostCurveOperator d hd h_missing zLeft z₀ h
      h_positive h_tendsto v hPLeft hPZero hvP hNLeft hAnchor hNZero hvN h_pairing
  have hNmax : Maximal C0Seq.coordinateDualPairing.IsMonotone
      (C0Seq.coordinateDualPairing.normalConeGraph C0Seq.finalConstraint) := by
    simpa only [C0Seq.finalConstraint] using
      (DualPairing.maximalMonotone_normalConeGraph_closedBall
        C0Seq.coordinateDualPairing C0Seq.coordinateDualPairing_surjective
        (1 / 2 : ℝ) (by norm_num))
  have hqual : Set.Nonempty
      (M.dom ∩ interior
        (C0Seq.coordinateDualPairing.normalConeDom C0Seq.finalConstraint)) := by
    dsimp [M]
    have hq := ghostCurveOperator_constraintQualification d hd h_missing zLeft z₀ h
      h_tendsto v hvP hvX
    simpa only [C0Seq.normalConeDom_finalConstraint] using hq
  have hsum_nonmax : ¬ Maximal C0Seq.coordinateDualPairing.IsMonotone
      (M + C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph := by
    dsimp [M]
    exact not_maximalMonotone_ghostCurveSum d hd h_missing zLeft z₀
      hPLeft hPZero hNLeft hNZero hLeft hZero h h_positive h_tendsto v hvP hvN
      hz₀_mem hqZero hMmax.1
  have hpolar : (0, 0) ∈ C0Seq.monotonePolar
      (M + C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph := by
    dsimp [M]
    exact zero_mem_monotonePolar_ghostCurveSum d hd h_missing zLeft z₀
      hPLeft hPZero hNLeft hNZero hLeft hZero h h_positive h_tendsto v hvP hvN
  have hzero_not_graph : (0, 0) ∉
      (M + C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph := by
    exact C0Seq.zero_not_mem_add_normalCone_graph_of_quadraticPairing_neg
      M (z₀ : C0Seq × L1Seq) hz₀_mem hqZero hMmax.1
  refine ⟨M, ⟨hMmax, hNmax⟩, ⟨hqual, hsum_nonmax, ?_⟩⟩
  exact ⟨hpolar, hzero_not_graph⟩

/-- The interior-domain maximal-monotone sum assertion fails already on real
`c₀`, with its continuous dual represented by real `ℓ¹`: two maximally
monotone operators can have `M.dom ∩ interior N.dom` nonempty while their
pointwise sum is not maximally monotone. -/
theorem exists_maximalMonotone_pair_sum_not_maximal :
    ∃ M N : SetValuedOperator C0Seq L1Seq,
      Maximal C0Seq.coordinateDualPairing.IsMonotone M.graph ∧
      Maximal C0Seq.coordinateDualPairing.IsMonotone N.graph ∧
      Set.Nonempty (M.dom ∩ interior N.dom) ∧
      ¬ Maximal C0Seq.coordinateDualPairing.IsMonotone (M + N).graph := by
  obtain ⟨M, ⟨hMmax, hNmax⟩, ⟨hqual, hsum_nonmax, _⟩⟩ :=
    exists_ghostCurveCounterexample
  let N : SetValuedOperator C0Seq L1Seq :=
    C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint
  have hNgraph : N.graph =
      C0Seq.coordinateDualPairing.normalConeGraph C0Seq.finalConstraint := by
    ext z
    rcases z with ⟨x, xstar⟩
    dsimp [N]
    rw [SetValuedOperator.mem_graph]
    rw [C0Seq.coordinateDualPairing.mem_normalCone]
    rw [C0Seq.coordinateDualPairing.mem_graph_normalCone]
  have hNdom : N.dom =
      C0Seq.coordinateDualPairing.normalConeDom C0Seq.finalConstraint := by
    ext x
    constructor
    · intro hx
      rw [SetValuedOperator.mem_dom] at hx
      obtain ⟨xstar, hxstar⟩ := hx
      apply (C0Seq.coordinateDualPairing.mem_dom_normalCone
        C0Seq.finalConstraint x).mpr
      exact (C0Seq.coordinateDualPairing.mem_normalCone
        C0Seq.finalConstraint x xstar).mp hxstar |>.1
    · intro hx
      have hxConstraint :=
        (C0Seq.coordinateDualPairing.mem_dom_normalCone
          C0Seq.finalConstraint x).mp hx
      rw [SetValuedOperator.mem_dom]
      refine ⟨0, ?_⟩
      apply (C0Seq.coordinateDualPairing.mem_normalCone
        C0Seq.finalConstraint x 0).mpr
      constructor
      · exact hxConstraint
      · intro y hy
        simp [DualPairing.toLinearPairing_apply]
  refine Exists.intro M ?_
  refine Exists.intro N ?_
  constructor
  · exact hMmax
  constructor
  · rw [hNgraph]
    exact hNmax
  constructor
  · rw [hNdom]
    exact hqual
  · dsimp [N]
    exact hsum_nonmax
end Lorentz
