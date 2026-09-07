/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.RemoteBall
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.LorentzCone
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftAnchor.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.LorentzCone
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.Injective
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Ghost-curve localization

This module proves the remote-ball and local-energy consequences needed by the
monotonicity and sum arguments.
-/

public section

namespace Lorentz

/-- Every realized point on the assembled ghost curve with negative quadratic pairing
has its primal component in `C0Seq.remoteBall`. -/
theorem ghostCurveN_primal_mem_remoteBall_of_quadraticPairing_neg
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (z : parametrizedSubspace d)
    (h_curve : negativeCoordinate d hd z =
      ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (positiveCoordinate d hd z))
    (h_neg : C0Seq.quadraticPairing z < 0) :
    z.1.1 ∈ C0Seq.remoteBall := by
  have hline_embed (u₀ u₁ : parametrizedSubspace d) (α : ℝ) :
      embedding d hd (AffineMap.lineMap u₀ u₁ α) =
        AffineMap.lineMap (embedding d hd u₀) (embedding d hd u₁) α := by
    simp only [embedding_apply, AffineMap.lineMap_apply_module, map_add, map_smul,
      Prod.smul_mk]
  have hreal :
      (positiveCoordinate d hd z,
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd z)) = embedding d hd z := by
    rw [embedding_apply]
    exact Prod.ext rfl h_curve.symm
  have hq : C0Seq.quadraticPairing z =
      positiveCoordinate d hd z ^ 2 -
        ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd z)‖ ^ 2 := by
    calc
      C0Seq.quadraticPairing z =
          positiveCoordinate d hd z ^ 2 - ‖negativeCoordinate d hd z‖ ^ 2 :=
        quadraticIdentity d hd z
      _ = positiveCoordinate d hd z ^ 2 -
          ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
            (positiveCoordinate d hd z)‖ ^ 2 := by rw [h_curve]
  have hz_of_embedding (u : parametrizedSubspace d)
      (hu : embedding d hd u =
        (positiveCoordinate d hd z,
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
            (positiveCoordinate d hd z))) : z = u := by
    apply embedding_injective d hd
    exact hreal.symm.trans hu.symm
  have hq_of_energy (u : parametrizedSubspace d)
      (hE : 0 ≤ energy (embedding d hd u)) :
      0 ≤ C0Seq.quadraticPairing u := by
    rw [quadraticPairing_eq_energy d hd u]
    simpa only [embedding_apply] using hE
  by_cases hPast : positiveCoordinate d hd z ≤ (-1 : ℝ)
  · have hf := ghostCurveN_of_le_neg_one d hd h_missing zLeft z₀ h h_tendsto v
      (positiveCoordinate d hd z) hPast
    have hu : embedding d hd (pastRay d zLeft (positiveCoordinate d hd z)) =
        (positiveCoordinate d hd z,
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
            (positiveCoordinate d hd z)) := by
      rw [embedding_apply,
        positiveCoordinate_pastRay d hd zLeft hPLeft
          (positiveCoordinate d hd z) hPast,
        negativeCoordinate_pastRay d hd zLeft (positiveCoordinate d hd z), hf]
    have hzpast := hz_of_embedding (pastRay d zLeft (positiveCoordinate d hd z)) hu
    have hqpast := pastRay_quadraticPairing_nonneg d hd zLeft hPLeft hNLeft
      (positiveCoordinate d hd z) hPast
    have hqz : 0 ≤ C0Seq.quadraticPairing z := by
      rw [hzpast]
      exact hqpast
    exact False.elim ((not_lt_of_ge hqz) h_neg)
  · have hgtLeft : (-1 : ℝ) < positiveCoordinate d hd z := lt_of_not_ge hPast
    by_cases hLeZero : positiveCoordinate d hd z ≤ 0
    · have hI : positiveCoordinate d hd z ∈ Set.Icc (-1 : ℝ) 0 :=
        ⟨hgtLeft.le, hLeZero⟩
      have hf := ghostCurveN_of_mem_Icc_neg_one_zero d hd h_missing zLeft z₀ h
        h_tendsto v (positiveCoordinate d hd z) hI
      have hu : embedding d hd (AffineMap.lineMap zLeft z₀
          (positiveCoordinate d hd z + 1)) =
          (positiveCoordinate d hd z,
            ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
              (positiveCoordinate d hd z)) := by
        rw [hline_embed, embedding_apply, embedding_apply, hPLeft, hPZero, hf]
        simp only [AffineMap.lineMap_apply_module, Prod.smul_mk]
        apply Prod.ext
        · simp only [Prod.fst_add]
          ring
        · simp only [Prod.snd_add]
      have hzline := hz_of_embedding
        (AffineMap.lineMap zLeft z₀ (positiveCoordinate d hd z + 1)) hu
      rw [hzline]
      exact (leftAnchorEdge_primal_mem_remoteBall d hd zLeft z₀ hPLeft hPZero
        hLeft hZero) hI
    · have hPos : 0 < positiveCoordinate d hd z := lt_of_not_ge hLeZero
      by_cases hBelowOne : positiveCoordinate d hd z < 1
      · by_cases hLeLeft0 : positiveCoordinate d hd z ≤ leftTime 0
        · have hI : positiveCoordinate d hd z ∈ Set.Icc (0 : ℝ) (leftTime 0) :=
            ⟨hPos.le, hLeLeft0⟩
          have hf := ghostCurveN_of_mem_Icc_zero_leftTime d hd h_missing zLeft z₀ h
            h_tendsto v (positiveCoordinate d hd z) hI
          have htime0 : (0 : ℝ) < leftTime 0 := by
            rw [leftTime_def]
            have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
            norm_num [Real.rpow_neg htwo_nonneg]
          have hratio :
              ((positiveCoordinate d hd z - 0) / (leftTime 0 - 0)) * leftTime 0 =
                positiveCoordinate d hd z := by
            field_simp [ne_of_gt htime0]
            ring
          have hu : embedding d hd
              (AffineMap.lineMap z₀ (leftVertex d hd h_missing z₀ 0)
                ((positiveCoordinate d hd z - 0) / (leftTime 0 - 0))) =
              (positiveCoordinate d hd z,
                ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
                  (positiveCoordinate d hd z)) := by
            rw [hline_embed, embedding_apply, embedding_apply, hPZero,
              positiveCoordinate_leftVertex d hd h_missing z₀ 0, hf]
            simp only [AffineMap.lineMap_apply_module, Prod.smul_mk]
            apply Prod.ext
            · simp only [Prod.fst_add]
              simp only [smul_eq_mul, mul_zero, zero_add]
              simpa only [sub_zero] using hratio
            · simp only [Prod.snd_add]
              simp only [sub_zero]
          have hzline := hz_of_embedding
            (AffineMap.lineMap z₀ (leftVertex d hd h_missing z₀ 0)
              ((positiveCoordinate d hd z - 0) / (leftTime 0 - 0))) hu
          rw [hzline]
          exact (initialLeftVertexEdge_primal_mem_remoteBall d hd h_missing z₀
            hPZero hZero) hI
        · have hLeft0Lt : leftTime 0 < positiveCoordinate d hd z :=
            lt_of_not_ge hLeLeft0
          have hidx := leftEdgeIndex_spec (positiveCoordinate d hd z) hLeft0Lt hBelowOne
          have hI : positiveCoordinate d hd z ∈
              Set.Icc (leftTime (leftEdgeIndex (positiveCoordinate d hd z)))
                (leftTime (leftEdgeIndex (positiveCoordinate d hd z) + 1)) :=
            ⟨hidx.1.le, hidx.2⟩
          have hf := ghostCurveN_of_mem_Icc_leftTime d hd h_missing zLeft z₀ h
            h_tendsto v (leftEdgeIndex (positiveCoordinate d hd z))
            (positiveCoordinate d hd z) hI
          have hgap : 0 < leftTime (leftEdgeIndex (positiveCoordinate d hd z) + 1) -
              leftTime (leftEdgeIndex (positiveCoordinate d hd z)) := by
            rw [leftTime_succ_sub]
            positivity
          have hratio :
              (1 - ((positiveCoordinate d hd z -
                leftTime (leftEdgeIndex (positiveCoordinate d hd z))) /
                (leftTime (leftEdgeIndex (positiveCoordinate d hd z) + 1) -
                  leftTime (leftEdgeIndex (positiveCoordinate d hd z))))) *
                  leftTime (leftEdgeIndex (positiveCoordinate d hd z)) +
                ((positiveCoordinate d hd z -
                  leftTime (leftEdgeIndex (positiveCoordinate d hd z))) /
                  (leftTime (leftEdgeIndex (positiveCoordinate d hd z) + 1) -
                    leftTime (leftEdgeIndex (positiveCoordinate d hd z)))) *
                  leftTime (leftEdgeIndex (positiveCoordinate d hd z) + 1) =
                positiveCoordinate d hd z := by
            field_simp [ne_of_gt hgap]
            ring
          let u : parametrizedSubspace d := AffineMap.lineMap
                (leftVertex d hd h_missing z₀ (leftEdgeIndex (positiveCoordinate d hd z)))
                (leftVertex d hd h_missing z₀
                  (leftEdgeIndex (positiveCoordinate d hd z) + 1))
                ((positiveCoordinate d hd z -
                  leftTime (leftEdgeIndex (positiveCoordinate d hd z))) /
                  (leftTime (leftEdgeIndex (positiveCoordinate d hd z) + 1) -
                    leftTime (leftEdgeIndex (positiveCoordinate d hd z))))
          have hu : embedding d hd u =
              (positiveCoordinate d hd z,
                ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
                (positiveCoordinate d hd z)) := by
            dsimp [u]
            rw [hline_embed, embedding_apply, embedding_apply,
              positiveCoordinate_leftVertex d hd h_missing z₀
                (leftEdgeIndex (positiveCoordinate d hd z)),
              positiveCoordinate_leftVertex d hd h_missing z₀
                (leftEdgeIndex (positiveCoordinate d hd z) + 1), hf]
            simp only [AffineMap.lineMap_apply_module, Prod.smul_mk]
            apply Prod.ext
            · simp only [Prod.fst_add, smul_eq_mul]
              exact hratio
            · simp only [Prod.snd_add]
          have hzline := hz_of_embedding u hu
          rw [hzline]
          exact (leftVertexEdge_primal_mem_remoteBall d hd h_missing z₀
            (leftEdgeIndex (positiveCoordinate d hd z))) hI
      · have hGeOne : 1 ≤ positiveCoordinate d hd z := le_of_not_gt hBelowOne
        by_cases hEqOne : positiveCoordinate d hd z = 1
        · have hf := ghostCurveN_one d hd h_missing zLeft z₀ h h_tendsto v
          have hqz : 0 ≤ C0Seq.quadraticPairing z := by
            rw [hq, hEqOne, hf]
            norm_num
          exact False.elim ((not_lt_of_ge hqz) h_neg)
        · have hGtOne : 1 < positiveCoordinate d hd z := lt_of_le_of_ne hGeOne
            (Ne.symm hEqOne)
          by_cases hLeRight : positiveCoordinate d hd z ≤ DetectorTriple.rightTime 0
          · have hidx := rightEdgeIndex_spec (positiveCoordinate d hd z) hGtOne hLeRight
            have hI : positiveCoordinate d hd z ∈
                Set.Icc (DetectorTriple.rightTime (rightEdgeIndex
                    (positiveCoordinate d hd z) + 1))
                  (DetectorTriple.rightTime (rightEdgeIndex
                    (positiveCoordinate d hd z))) :=
              ⟨hidx.1, hidx.2⟩
            have hf := ghostCurveN_of_mem_Icc_rightTime d hd h_missing zLeft z₀ h
              h_tendsto v (rightEdgeIndex (positiveCoordinate d hd z))
              (positiveCoordinate d hd z) hI
            have hgap : 0 < DetectorTriple.rightTime (rightEdgeIndex
                (positiveCoordinate d hd z)) - DetectorTriple.rightTime
                  (rightEdgeIndex (positiveCoordinate d hd z) + 1) := by
              rw [DetectorTriple.rightTime_sub_succ]
              positivity
            have hratio :
                (1 - ((positiveCoordinate d hd z -
                  DetectorTriple.rightTime (rightEdgeIndex
                    (positiveCoordinate d hd z) + 1)) /
                  (DetectorTriple.rightTime (rightEdgeIndex
                    (positiveCoordinate d hd z)) - DetectorTriple.rightTime
                      (rightEdgeIndex (positiveCoordinate d hd z) + 1)))) *
                    DetectorTriple.rightTime (rightEdgeIndex
                      (positiveCoordinate d hd z) + 1) +
                  ((positiveCoordinate d hd z -
                    DetectorTriple.rightTime (rightEdgeIndex
                      (positiveCoordinate d hd z) + 1)) /
                    (DetectorTriple.rightTime (rightEdgeIndex
                      (positiveCoordinate d hd z)) - DetectorTriple.rightTime
                        (rightEdgeIndex (positiveCoordinate d hd z) + 1))) *
                    DetectorTriple.rightTime (rightEdgeIndex
                      (positiveCoordinate d hd z)) =
                  positiveCoordinate d hd z := by
              field_simp [ne_of_gt hgap]
              ring
            let u : parametrizedSubspace d := AffineMap.lineMap
              (rightVertex d hd h_missing h h_tendsto
                (rightEdgeIndex (positiveCoordinate d hd z) + 1))
              (rightVertex d hd h_missing h h_tendsto
                (rightEdgeIndex (positiveCoordinate d hd z)))
              ((positiveCoordinate d hd z - DetectorTriple.rightTime
                (rightEdgeIndex (positiveCoordinate d hd z) + 1)) /
                (DetectorTriple.rightTime (rightEdgeIndex
                  (positiveCoordinate d hd z)) - DetectorTriple.rightTime
                  (rightEdgeIndex (positiveCoordinate d hd z) + 1)))
            have hu : embedding d hd u =
                (positiveCoordinate d hd z,
                  ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
                    (positiveCoordinate d hd z)) := by
              dsimp [u]
              rw [hline_embed, embedding_apply, embedding_apply,
                positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto
                  (rightEdgeIndex (positiveCoordinate d hd z) + 1),
                positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto
                  (rightEdgeIndex (positiveCoordinate d hd z)), hf]
              simp only [AffineMap.lineMap_apply_module, Prod.smul_mk]
              apply Prod.ext
              · simp only [Prod.fst_add, smul_eq_mul]
                exact hratio
              · simp only [Prod.snd_add]
            have hzline := hz_of_embedding u hu
            have hE := rightVertexEdge_energy_nonneg d hd h_missing h h_positive
              h_tendsto (rightEdgeIndex (positiveCoordinate d hd z))
              (positiveCoordinate d hd z) hI
            have hE' : 0 ≤ energy (embedding d hd u) := by
              rw [hline_embed]
              exact hE
            have hqz : 0 ≤ C0Seq.quadraticPairing z := by
              rw [hzline]
              exact hq_of_energy u hE'
            exact False.elim ((not_lt_of_ge hqz) h_neg)
          · have hGtRight : DetectorTriple.rightTime 0 < positiveCoordinate d hd z :=
              lt_of_not_ge hLeRight
            by_cases hLeTwo : positiveCoordinate d hd z ≤ 2
            · have hrt0 : DetectorTriple.rightTime 0 = (3 / 2 : ℝ) := by
                rw [DetectorTriple.rightTime_def]
                have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
                norm_num [Real.rpow_neg htwo_nonneg]
              have hI : positiveCoordinate d hd z ∈
                  Set.Icc (DetectorTriple.rightTime 0) 2 :=
                ⟨hGtRight.le, hLeTwo⟩
              have hI' : positiveCoordinate d hd z ∈
                  Set.Icc (3 / 2 : ℝ) 2 := by
                rw [← hrt0]
                exact hI
              have hf := ghostCurveN_of_mem_Icc_rightTime_zero_two d hd h_missing
                zLeft z₀ h h_tendsto v (positiveCoordinate d hd z) hI
              have hgap : 0 < 2 - DetectorTriple.rightTime 0 := by
                rw [hrt0]
                norm_num
              have hratio :
                  (1 - ((positiveCoordinate d hd z - DetectorTriple.rightTime 0) /
                    (2 - DetectorTriple.rightTime 0))) * DetectorTriple.rightTime 0 +
                    ((positiveCoordinate d hd z - DetectorTriple.rightTime 0) /
                      (2 - DetectorTriple.rightTime 0)) * 2 =
                    positiveCoordinate d hd z := by
                field_simp [ne_of_gt hgap]
                ring
              let u : parametrizedSubspace d := AffineMap.lineMap
                (rightVertex d hd h_missing h h_tendsto 0) ((2 : ℝ) • v)
                ((positiveCoordinate d hd z - DetectorTriple.rightTime 0) /
                  (2 - DetectorTriple.rightTime 0))
              have hu : embedding d hd u =
                  (positiveCoordinate d hd z,
                    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
                      (positiveCoordinate d hd z)) := by
                dsimp [u]
                rw [hline_embed, embedding_apply, embedding_apply,
                  positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto 0,
                  map_smul, hvP, hf]
                simp only [AffineMap.lineMap_apply_module, Prod.smul_mk]
                apply Prod.ext
                · simp only [Prod.fst_add, smul_eq_mul]
                  simpa only [mul_one] using hratio
                · simp only [Prod.snd_add]
              have hzline := hz_of_embedding u hu
              have hE := foldedToFutureEdge_energy_nonneg d hd h_missing h
                h_positive h_tendsto v hvP hvN (positiveCoordinate d hd z) hI'
              have hE' : 0 ≤ energy (embedding d hd u) := by
                rw [hline_embed]
                simpa only [hrt0] using hE
              have hqz : 0 ≤ C0Seq.quadraticPairing z := by
                rw [hzline]
                exact hq_of_energy u hE'
              exact False.elim ((not_lt_of_ge hqz) h_neg)
            · have hPtwo : 2 ≤ positiveCoordinate d hd z := le_of_not_ge hLeTwo
              have hf := ghostCurveN_of_two_le d hd h_missing zLeft z₀ h h_tendsto v
                (positiveCoordinate d hd z) hPtwo
              have hu : embedding d hd
                  ((positiveCoordinate d hd z) • v) =
                  (positiveCoordinate d hd z,
                    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
                      (positiveCoordinate d hd z)) := by
                rw [embedding_apply, map_smul, hvP, map_smul, hf]
                simp only [smul_eq_mul, mul_one]
              have hzline := hz_of_embedding
                ((positiveCoordinate d hd z) • v) hu
              have hE := futureRay_energy_nonneg d hd v hvP hvN
                (positiveCoordinate d hd z) hPtwo
              have hqz : 0 ≤ C0Seq.quadraticPairing z := by
                rw [hzline]
                exact hq_of_energy ((positiveCoordinate d hd z) • v) hE
              exact False.elim ((not_lt_of_ge hqz) h_neg)

/-- Every realized point on the assembled ghost curve whose primal component lies in
`C0Seq.localOpenUnitBall` has nonnegative quadratic pairing. -/
theorem ghostCurveN_quadraticPairing_nonneg_of_primal_mem_localBall
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (hNZero : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (z : parametrizedSubspace d)
    (h_curve : negativeCoordinate d hd z =
      ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (positiveCoordinate d hd z))
    (h_local : z.1.1 ∈ C0Seq.localOpenUnitBall) :
    0 ≤ C0Seq.quadraticPairing z := by
  by_contra h_nonneg
  have h_neg : C0Seq.quadraticPairing z < 0 := lt_of_not_ge h_nonneg
  have h_remote := ghostCurveN_primal_mem_remoteBall_of_quadraticPairing_neg
    d hd h_missing zLeft z₀ hPLeft hPZero hNLeft hNZero hLeft hZero h
    h_positive h_tendsto v hvP hvN z h_curve h_neg
  exact Set.disjoint_left.1 C0Seq.localOpenUnitBall_disjoint_remoteBall
    h_local h_remote

/-- A parametrized point realizing the assembled ghost curve has nonnegative
quadratic pairing whenever its primal coordinate lies in
`C0Seq.localOpenUnitBall`. -/
theorem ghostCurveN_localEnergy_nonneg
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (hNZero : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (m : parametrizedSubspace d)
    (h_realize :
      (P, ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P) = embedding d hd m)
    (h_local : m.1.1 ∈ C0Seq.localOpenUnitBall) :
    0 ≤ C0Seq.quadraticPairing m := by
  have hP : positiveCoordinate d hd m = P := by
    have hfst := congrArg Prod.fst h_realize
    rw [embedding_apply] at hfst
    exact hfst.symm
  have h_curve : negativeCoordinate d hd m =
      ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (positiveCoordinate d hd m) := by
    have hsnd := congrArg Prod.snd h_realize
    rw [embedding_apply] at hsnd
    simpa [hP] using hsnd.symm
  exact ghostCurveN_quadraticPairing_nonneg_of_primal_mem_localBall
    d hd h_missing zLeft z₀ hPLeft hPZero hNLeft hNZero hLeft hZero h
    h_positive h_tendsto v hvP hvN m h_curve h_local

end Lorentz
