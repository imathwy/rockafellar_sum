/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.Group.Sequences
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph.RightVertex
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Continuity
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Asymptotics
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.Axis
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Monotone-polar constraints for the ghost curve

This module uses detector asymptotics and the Lorentz axis to constrain points
in the monotone polar of the ghost-curve operator graph.
-/

public section

namespace Lorentz

/-- Every point in the monotone polar of the graph of the ghost-curve operator
belongs to the subspace used in its parametrization. -/
theorem mem_parametrizedSubspace_of_mem_ghostCurveOperator_polar
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (w : C0Seq × L1Seq)
    (h_polar : w ∈ C0Seq.monotonePolar
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (h_pairing : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w))) :
    w ∈ parametrizedSubspace d := by
  by_contra hw
  have h_polar_ghost : w ∈ C0Seq.monotonePolar
      (ghostGraph d hd h_missing zLeft z₀ h h_tendsto v) := by
    rw [← graph_ghostCurveOperator]
    exact h_polar
  obtain ⟨i, hi, hgap⟩ :=
    rightVertex_sub_quadraticPairing_cofinal d hd h_missing w hw h h_positive
      h_tendsto h_pairing (C0Seq.quadraticPairing w) 0
  have hbound :=
    rightVertex_gap_le d hd h_missing zLeft z₀ h h_positive h_tendsto v w
      h_polar_ghost i
  linarith

/-- A point of the parametrized Lorentz subspace in the monotone polar of the
ghost-curve operator graph cannot have positive coordinate `1`. -/
theorem positiveCoordinate_ne_one_of_mem_ghostCurveOperator_polar
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (h_z₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (w : parametrizedSubspace d)
    (h_polar : w.val ∈ C0Seq.monotonePolar
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph) :
    positiveCoordinate d hd w ≠ 1 := by
  intro hP
  have hcont : ContinuousAt
      (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v) 1 :=
    (continuous_ghostCurveN d hd h_missing zLeft z₀ h_z₀ h h_tendsto v).continuousAt
  have hcurve_one :
      ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 1 = 0 :=
    ghostCurveN_one d hd h_missing zLeft z₀ h h_tendsto v
  have hright_tendsto :
      Filter.Tendsto (fun i : ℕ => DetectorTriple.rightTime i) Filter.atTop (nhds (1 : ℝ)) := by
    have hexp : Filter.Tendsto (fun i : ℕ => -((i : ℝ) + 1)) Filter.atTop Filter.atBot := by
      exact Filter.tendsto_neg_atTop_atBot.comp
        (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hpow : Filter.Tendsto (fun x : ℝ => (2 : ℝ) ^ x) Filter.atBot (nhds 0) :=
      tendsto_rpow_atBot_of_base_gt_one (2 : ℝ) (by norm_num)
    have hpow' := hpow.comp hexp
    simpa only [DetectorTriple.rightTime_def, Function.comp_apply, add_zero] using
      hpow'.const_add 1
  have hright_ne : ∀ i : ℕ, DetectorTriple.rightTime i ≠ (1 : ℝ) := by
    intro i hi
    rw [DetectorTriple.rightTime_def] at hi
    have hpos : 0 < (2 : ℝ) ^ (-(i : ℝ) + (-1)) := by positivity
    have hexp : -(i : ℝ) + (-1) = -((i : ℝ) + 1) := by ring
    rw [hexp] at hpos
    linarith
  have hNzero : negativeCoordinate d hd w = 0 := by
    apply eq_zero_of_tendsto_sq_norm_bound
      (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
      (negativeCoordinate d hd w)
      (fun i : ℕ => DetectorTriple.rightTime i)
      hcont hcurve_one hright_tendsto hright_ne
    intro i hi
    let rv : parametrizedSubspace d :=
      rightVertex d hd h_missing h h_tendsto i
    have hrv_ghost : rv.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
      simpa [rv] using
        (rightVertex_mem_ghostGraph d hd h_missing zLeft z₀ h h_positive h_tendsto v i)
    have hrv_graph : rv.val ∈
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph := by
      rw [graph_ghostCurveOperator]
      exact hrv_ghost
    have hpolar_i : 0 ≤ C0Seq.quadraticPairing (w.val - rv.val) := by
      have hp := (C0Seq.mem_monotonePolar _ w.val).1 h_polar
      exact hp rv.val hrv_graph
    have hquad := quadraticIdentity d hd (w - rv)
    change C0Seq.quadraticPairing (w.val - rv.val) = _ at hquad
    have hP_rv : positiveCoordinate d hd rv = DetectorTriple.rightTime i := by
      simpa [rv] using
        (positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto i)
    have hN_rv : negativeCoordinate d hd rv =
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (DetectorTriple.rightTime i) := by
      simpa [rv] using
        (ghostCurveN_rightTime d hd h_missing zLeft z₀ h h_tendsto v i).symm
    have hPdiff : positiveCoordinate d hd (w - rv) =
        1 - DetectorTriple.rightTime i := by
      rw [map_sub, hP, hP_rv]
    have hNdiff : negativeCoordinate d hd (w - rv) =
        negativeCoordinate d hd w -
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
            (DetectorTriple.rightTime i) := by
      rw [map_sub, hN_rv]
    rw [hPdiff, hNdiff] at hquad
    rw [hquad] at hpolar_i
    exact hpolar_i
  have hmem_axis : (1, 0) ∈ embeddingRange d hd := by
    rw [mem_embeddingRange]
    refine ⟨w, ?_⟩
    rw [embedding_apply, hP, hNzero]
  exact (axis_not_mem_embeddingRange d hd 1 one_ne_zero) hmem_axis

end Lorentz
