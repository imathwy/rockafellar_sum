/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Monotonicity of the ghost-curve operator

This module expresses quadratic differences along the ghost graph in Lorentz
coordinates and proves monotonicity of the associated operator.
-/

public section

namespace Lorentz

/-- For two points of the ghost graph, the quadratic pairing of their difference
is the squared difference of their positive coordinates minus the squared norm
of the corresponding difference along the negative-coordinate ghost curve. -/
theorem quadraticPairing_sub_mem_ghostGraph
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v mP mQ : parametrizedSubspace d)
    (hmP : mP.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v)
    (hmQ : mQ.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v) :
    C0Seq.quadraticPairing (mP - mQ) =
      (positiveCoordinate d hd mP - positiveCoordinate d hd mQ) ^ 2 -
        ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
              (positiveCoordinate d hd mP) -
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
              (positiveCoordinate d hd mQ)‖ ^ 2 := by
  have hP := (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v mP).mp hmP
  have hQ := (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v mQ).mp hmQ
  have hco : ((mP - mQ : parametrizedSubspace d) : C0Seq × L1Seq) =
      (mP : C0Seq × L1Seq) - (mQ : C0Seq × L1Seq) :=
    Submodule.coe_sub (parametrizedSubspace d) mP mQ
  rw [← hco, quadraticIdentity d hd (mP - mQ)]
  rw [(positiveCoordinate d hd).map_sub, (negativeCoordinate d hd).map_sub]
  rw [hP.2, hQ.2]

/-- The ghost-curve operator is monotone with respect to the coordinate dual
pairing. -/
theorem isMonotone_ghostCurveOperator
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (h_zLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (h_anchor : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (h_z₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (h_v : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16) :
    C0Seq.coordinateDualPairing.IsMonotone
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph := by
  apply (DualPairing.isMonotone_iff_subset_polar
    C0Seq.coordinateDualPairing
    (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph).2
  intro z hz
  rw [DualPairing.mem_monotonePolar]
  intro w hw
  rw [graph_ghostCurveOperator] at hz hw
  rw [ghostGraph_eq_preimage_graphOn] at hz hw
  rcases hz with ⟨mP, hmP, hPval⟩
  rcases hw with ⟨mQ, hmQ, hQval⟩
  subst z
  subst w
  have hmP' : mP.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
    apply (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v mP).2
    rw [Set.mem_preimage, Set.mem_graphOn] at hmP
    rw [embedding_apply] at hmP
    exact ⟨hmP.1, hmP.2.symm⟩
  have hmQ' : mQ.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
    apply (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v mQ).2
    rw [Set.mem_preimage, Set.mem_graphOn] at hmQ
    rw [embedding_apply] at hmQ
    exact ⟨hmQ.1, hmQ.2.symm⟩
  have hq := quadraticPairing_sub_mem_ghostGraph d hd h_missing zLeft z₀ h
    h_tendsto v mP mQ hmP' hmQ'
  rw [← C0Seq.quadraticPairing_eq_coordinateQuadratic]
  rw [hq]
  have hL := (lipschitzWith_ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
    h_zLeft h_anchor h_z₀ h_v).dist_le_mul
      (positiveCoordinate d hd mP) (positiveCoordinate d hd mQ)
  have hL' :
      ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd mP) -
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd mQ)‖ ≤
        |positiveCoordinate d hd mP - positiveCoordinate d hd mQ| := by
    simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using hL
  have hsq :
      ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd mP) -
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd mQ)‖ ^ 2 ≤
        (positiveCoordinate d hd mP - positiveCoordinate d hd mQ) ^ 2 := by
    simpa only [sq_abs] using
      ((sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mpr hL')
  exact sub_nonneg.mpr hsq

end Lorentz
