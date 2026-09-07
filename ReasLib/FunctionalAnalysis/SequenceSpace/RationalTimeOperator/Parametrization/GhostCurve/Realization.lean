/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.Injective
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Realization of the assembled ghost curve

This module proves that non-ghost curve parameters are realized by points of
the Lorentz embedding and establishes uniqueness and energy formulas.
-/

public section

namespace Lorentz

/-- Away from ghost time, the parameter and the assembled negative-coordinate curve
form a point in the range of the Lorentz embedding. -/
theorem ghostCurveN_mem_embeddingRange (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (P : ℝ) (hP : P ≠ 1) :
    (P, ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P) ∈
      embeddingRange d hd := by
  have range_at : ∀ (z : parametrizedSubspace d) {P : ℝ},
      positiveCoordinate d hd z = P →
        (P, negativeCoordinate d hd z) ∈ embeddingRange d hd := by
    intro z P hcoord
    rw [mem_embeddingRange]
    refine ⟨z, ?_⟩
    rw [embedding_apply]
    exact Prod.ext hcoord rfl
  have hzLeftRange :
      (-1, negativeCoordinate d hd zLeft) ∈ embeddingRange d hd :=
    range_at zLeft hPLeft
  have hzZeroRange :
      (0, negativeCoordinate d hd z₀) ∈ embeddingRange d hd :=
    range_at z₀ hPZero
  have hleftVertexRange (k : ℕ) :
      (leftTime k,
        negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)) ∈
        embeddingRange d hd :=
    range_at (leftVertex d hd h_missing z₀ k)
      (positiveCoordinate_leftVertex d hd h_missing z₀ k)
  have hrightVertexRange (i : ℕ) :
      (DetectorTriple.rightTime i,
        negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i)) ∈
        embeddingRange d hd :=
    range_at (rightVertex d hd h_missing h h_tendsto i)
      (positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto i)
  have htwoCoord : positiveCoordinate d hd ((2 : ℝ) • v) = 2 := by
    rw [map_smul, hvP]
    norm_num
  have htwoRange :
      (2, negativeCoordinate d hd ((2 : ℝ) • v)) ∈ embeddingRange d hd :=
    range_at ((2 : ℝ) • v) htwoCoord
  have htwoRange' :
      (2, (2 : ℝ) • negativeCoordinate d hd v) ∈ embeddingRange d hd := by
    simpa only [map_smul] using htwoRange
  by_cases hpast : P ≤ -1
  · rw [ghostCurveN_of_le_neg_one d hd h_missing zLeft z₀ h h_tendsto v P hpast]
    rw [← negativeCoordinate_pastRay d hd zLeft P]
    exact pastRay_mem_embeddingRange d hd zLeft hPLeft P
  · have hgtneg : -1 < P := lt_of_not_ge hpast
    by_cases hbelowone : P < 1
    · by_cases hleftanchor : P ≤ 0
      · by_cases hleft_eq : P = 0
        · subst P
          rw [ghostCurveN_zero d hd h_missing zLeft z₀ h h_tendsto v]
          exact hzZeroRange
        · have hPneg : -1 < P ∧ P < 0 :=
            ⟨hgtneg, lt_of_le_of_ne hleftanchor hleft_eq⟩
          rw [ghostCurveN_of_mem_Icc_neg_one_zero d hd h_missing zLeft z₀ h h_tendsto v P
            ⟨le_of_lt hPneg.1, le_of_lt hPneg.2⟩]
          have hratio : (P - (-1 : ℝ)) / (0 - (-1 : ℝ)) = P + 1 := by ring
          rw [← hratio]
          apply affineInterpolation_mem_embeddingRange d hd
            (P₀ := (-1 : ℝ)) (P₁ := 0) (P := P)
            (N₀ := negativeCoordinate d hd zLeft)
            (N₁ := negativeCoordinate d hd z₀)
          · exact hzLeftRange
          · exact hzZeroRange
          · exact ⟨by linarith, by linarith⟩
      · have hPpos : 0 < P := lt_of_not_ge hleftanchor
        by_cases hleft : P ≤ leftTime 0
        · by_cases heq : P = leftTime 0
          · subst P
            rw [ghostCurveN_leftTime d hd h_missing zLeft z₀ h h_tendsto v 0]
            exact hleftVertexRange 0
          · have hlt : P < leftTime 0 := lt_of_le_of_ne hleft heq
            rw [ghostCurveN_of_mem_Icc_zero_leftTime d hd h_missing zLeft z₀ h h_tendsto v P
              ⟨le_of_lt hPpos, hleft⟩]
            have hratio : (P - 0) / (leftTime 0 - 0) = P / leftTime 0 := by
              simp
            rw [← hratio]
            apply affineInterpolation_mem_embeddingRange d hd
              (P₀ := 0) (P₁ := leftTime 0) (P := P)
              (N₀ := negativeCoordinate d hd z₀)
              (N₁ := negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0))
            · exact hzZeroRange
            · exact hleftVertexRange 0
            · exact ⟨hPpos, hlt⟩
        · have hleft_gt : leftTime 0 < P := lt_of_not_ge hleft
          have hidx := leftEdgeIndex_spec P hleft_gt hbelowone
          let k : ℕ := leftEdgeIndex P
          by_cases heq : P = leftTime (k + 1)
          · rw [heq]
            rw [ghostCurveN_leftTime d hd h_missing zLeft z₀ h h_tendsto v (k + 1)]
            exact hleftVertexRange (k + 1)
          · have hklower : leftTime k < P := by
              simpa [k] using hidx.1
            have hkupper : P < leftTime (k + 1) := lt_of_le_of_ne hidx.2 heq
            rw [ghostCurveN_of_mem_Icc_leftTime d hd h_missing zLeft z₀ h h_tendsto v k P
              ⟨le_of_lt hklower, le_of_lt hkupper⟩]
            exact affineInterpolation_mem_embeddingRange d hd
              (hleftVertexRange k) (hleftVertexRange (k + 1))
              ⟨hklower, hkupper⟩
    · have hgtone : 1 < P := lt_of_le_of_ne (le_of_not_gt hbelowone) (Ne.symm hP)
      by_cases hright : P ≤ DetectorTriple.rightTime 0
      · have hidx := rightEdgeIndex_spec P hgtone hright
        let i : ℕ := rightEdgeIndex P
        by_cases heqlower : P = DetectorTriple.rightTime (i + 1)
        · rw [heqlower]
          rw [ghostCurveN_rightTime d hd h_missing zLeft z₀ h h_tendsto v (i + 1)]
          exact hrightVertexRange (i + 1)
        · by_cases hequpper : P = DetectorTriple.rightTime i
          · rw [hequpper]
            rw [ghostCurveN_rightTime d hd h_missing zLeft z₀ h h_tendsto v i]
            exact hrightVertexRange i
          · have hilower : DetectorTriple.rightTime (i + 1) < P :=
              lt_of_le_of_ne hidx.1 (Ne.symm heqlower)
            have hiupper : P < DetectorTriple.rightTime i :=
              lt_of_le_of_ne hidx.2 hequpper
            rw [ghostCurveN_of_mem_Icc_rightTime d hd h_missing zLeft z₀ h h_tendsto v i P
              ⟨le_of_lt hilower, le_of_lt hiupper⟩]
            exact affineInterpolation_mem_embeddingRange d hd
              (hrightVertexRange (i + 1)) (hrightVertexRange i)
              ⟨hilower, hiupper⟩
      · have hright_gt : DetectorTriple.rightTime 0 < P := lt_of_not_ge hright
        by_cases houter : P ≤ 2
        · by_cases heqright : P = DetectorTriple.rightTime 0
          · rw [heqright]
            rw [ghostCurveN_rightTime d hd h_missing zLeft z₀ h h_tendsto v 0]
            exact hrightVertexRange 0
          · by_cases heqtwo : P = 2
            · rw [heqtwo]
              rw [ghostCurveN_two d hd h_missing zLeft z₀ h h_tendsto v]
              exact htwoRange'
            · have hleftstrict : DetectorTriple.rightTime 0 < P := hright_gt
              have hrightstrict : P < 2 := lt_of_le_of_ne houter heqtwo
              rw [ghostCurveN_of_mem_Icc_rightTime_zero_two d hd h_missing zLeft z₀ h h_tendsto v P
                ⟨le_of_lt hleftstrict, le_of_lt hrightstrict⟩]
              exact affineInterpolation_mem_embeddingRange d hd
                (hrightVertexRange 0) htwoRange
                ⟨hleftstrict, hrightstrict⟩
        · have hPge2 : 2 ≤ P := le_of_not_ge houter
          rw [ghostCurveN_of_two_le d hd h_missing zLeft z₀ h h_tendsto v P hPge2]
          simpa only [map_smul] using futureRay_mem_embeddingRange d hd v hvP P hPge2

/-- Every parameter other than ghost time is realized by a unique point of the
parametrized subspace with the prescribed positive and negative Lorentz coordinates. -/
theorem existsUnique_ghostCurveN_preimage (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (P : ℝ) (hP : P ≠ 1) :
    ∃! z : parametrizedSubspace d,
      positiveCoordinate d hd z = P ∧
        negativeCoordinate d hd z =
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P := by
  have hmem := ghostCurveN_mem_embeddingRange d hd h_missing zLeft z₀
    hPLeft hPZero h h_positive h_tendsto v hvP P hP
  rw [mem_embeddingRange] at hmem
  rcases hmem with ⟨z, hz⟩
  have hzcoords :
      positiveCoordinate d hd z = P ∧
        negativeCoordinate d hd z =
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P := by
    rw [embedding_apply] at hz
    exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  refine ⟨z, hzcoords, ?_⟩
  intro y hy
  apply embedding_injective d hd
  rw [embedding_apply, embedding_apply]
  exact Prod.ext (hy.1.trans hzcoords.1.symm) (hy.2.trans hzcoords.2.symm)

/-- If a parametrized point realizes the displayed coordinates of the assembled
ghost curve at `P`, then its quadratic pairing is `P ^ 2` minus the squared norm
of the negative coordinate. -/
theorem ghostCurveN_quadraticPairing_eq
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (P : ℝ) (m : parametrizedSubspace d)
    (h_realize :
      (P, ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P) = embedding d hd m) :
    C0Seq.quadraticPairing m =
      P ^ 2 - ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ^ 2 := by
  have hP : positiveCoordinate d hd m = P := by
    have hcoord := congrArg Prod.fst h_realize
    rw [embedding_apply] at hcoord
    exact hcoord.symm
  have hN : negativeCoordinate d hd m =
      ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P := by
    have hcoord := congrArg Prod.snd h_realize
    rw [embedding_apply] at hcoord
    exact hcoord.symm
  calc
    C0Seq.quadraticPairing m =
        positiveCoordinate d hd m ^ 2 - ‖negativeCoordinate d hd m‖ ^ 2 :=
      quadraticIdentity d hd m
    _ = P ^ 2 - ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ^ 2 := by
      rw [hP, hN]

end Lorentz
