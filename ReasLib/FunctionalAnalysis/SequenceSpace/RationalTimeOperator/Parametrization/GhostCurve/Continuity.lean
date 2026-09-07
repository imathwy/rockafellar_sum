/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Asymptotics
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Asymptotics
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.AffineInterpolation
public import ReasLib.Analysis.ChainInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay

/-!
# Continuity of the ghost curve

This module proves continuity of the assembled negative-coordinate curve,
including its accumulation time.
-/

public section

open Filter Topology

namespace Lorentz

/-- The global negative-coordinate ghost curve is continuous, including at the common
accumulation time of the left and right dyadic chains. -/
theorem continuous_ghostCurveN (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) :
    Continuous (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v) := by
  let f : ℝ → HilbertProd2 UnitL2 :=
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
  have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hneg_half_nonpos : (-(1 / 2 : ℝ)) ≤ 0 := by norm_num
  have ht0 : (0 : ℝ) < leftTime 0 := by
    rw [leftTime_def]
    norm_num [Real.rpow_neg htwo_nonneg]
  have ht01 : leftTime 0 < (1 : ℝ) := by
    rw [leftTime_def]
    norm_num [Real.rpow_neg htwo_nonneg]
  have hinitial_slope :
      ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
          negativeCoordinate d hd z₀‖ < leftTime 0 := by
    have hvertex := norm_negativeCoordinate_leftVertex_sub_leftTemplate_lt
      d hd h_missing z₀ 0
    have htime : leftTime 0 = (1 / 2 : ℝ) := by
      rw [leftTime_def]
      norm_num [Real.rpow_neg htwo_nonneg]
    have hrad : leftRadius 0 = (1 / 32 : ℝ) := by
      rw [leftRadius_def]
      norm_num [Real.rpow_neg htwo_nonneg]
    have htemplate :
        ‖leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
            negativeCoordinate d hd z₀‖ < (1 / 64 : ℝ) := by
      rw [htime, leftTemplate_apply]
      have hdiff : (1 - (1 / 2 : ℝ)) • negativeCoordinate d hd z₀ -
          negativeCoordinate d hd z₀ = -(1 / 2 : ℝ) • negativeCoordinate d hd z₀ := by
        module
      rw [hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos hneg_half_nonpos]
      nlinarith
    have hvertex' :
        ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
            leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)‖ <
          (1 / 32 : ℝ) := by
      exact lt_of_lt_of_eq hvertex hrad
    have hdecomp :
        negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
            negativeCoordinate d hd z₀ =
          (negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
              leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)) +
            (leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
              negativeCoordinate d hd z₀) := by
      module
    calc
      ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
          negativeCoordinate d hd z₀‖ =
          ‖(negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
              leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)) +
            (leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
              negativeCoordinate d hd z₀)‖ := congrArg norm hdecomp
      _ ≤ ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
            leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)‖ +
          ‖leftTemplate (negativeCoordinate d hd z₀) (leftTime 0) -
            negativeCoordinate d hd z₀‖ := norm_add_le _ _
      _ < leftTime 0 := by nlinarith [hvertex', htemplate, htime]
  have hinitial_endpoint_bound :
      ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
          negativeCoordinate d hd z₀‖ ≤ (1 : ℝ) * (leftTime 0 - 0) := by
    simpa only [NNReal.coe_one, one_mul, sub_zero] using hinitial_slope.le
  have hinit : LipschitzOnWith 1 f (Set.Icc (0 : ℝ) (leftTime 0)) := by
    have hline := AffineMap.lipschitzOnWith_lineMap_interval
      (K := (1 : NNReal)) ht0 hinitial_endpoint_bound
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_
    have hs' := ghostCurveN_of_mem_Icc_zero_leftTime d hd h_missing zLeft z₀ h
      h_tendsto v s hs
    have ht' := ghostCurveN_of_mem_Icc_zero_leftTime d hd h_missing zLeft z₀ h
      h_tendsto v t ht
    dsimp [f]
    rw [hs', ht']
    simpa only [sub_zero, div_one, one_mul, NNReal.coe_one] using
      hline.dist_le_mul s hs t ht
  have hleftChain : LipschitzOnWith 1 f (Set.Icc (leftTime 0) (1 : ℝ)) := by
    have hstep : ∀ n : ℕ, leftTime n < leftTime (n + 1) := by
      intro n
      rw [← sub_pos, leftTime_succ_sub]
      positivity
    have hmono : StrictMono leftTime := strictMono_nat_of_lt_succ hstep
    have hbelow : ∀ n, leftTime n < (1 : ℝ) := by
      intro n
      rw [leftTime_def]
      have hp : 0 < (2 : ℝ) ^ (-(n + 1 : ℝ)) := by positivity
      linarith
    have hleft_step_bound : ∀ n : ℕ,
        ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ (n + 1)) -
            negativeCoordinate d hd (leftVertex d hd h_missing z₀ n)‖ ≤
          (1 : ℝ) * |leftTime (n + 1) - leftTime n| := by
      intro n
      have hs := leftVertex_slope_lt_one d hd h_missing z₀ hN₀ n
      have hgap : 0 < leftTime (n + 1) - leftTime n := by
        rw [leftTime_succ_sub]
        positivity
      simpa only [NNReal.coe_one, one_mul, abs_of_pos hgap] using hs.le
    have hleft_endpoint : f 1 = 0 := by
      dsimp [f]
      exact ghostCurveN_one d hd h_missing zLeft z₀ h h_tendsto v
    have hleft_interpolation : ∀ n : ℕ, Set.EqOn f
        (fun s ↦ AffineMap.lineMap
          (negativeCoordinate d hd (leftVertex d hd h_missing z₀ n))
          (negativeCoordinate d hd (leftVertex d hd h_missing z₀ (n + 1)))
          ((s - leftTime n) / (leftTime (n + 1) - leftTime n)))
        (Set.Icc (leftTime n) (leftTime (n + 1))) := by
      intro n s hs
      dsimp [f]
      exact ghostCurveN_of_mem_Icc_leftTime d hd h_missing zLeft z₀ h h_tendsto v n s hs
    exact AffineMap.lipschitzOnWith_chainInterpolation_of_strictMono
      (E := HilbertProd2 UnitL2) (K := (1 : NNReal)) (a := (1 : ℝ))
      (t := leftTime)
      (x := fun n ↦ negativeCoordinate d hd (leftVertex d hd h_missing z₀ n))
      (x0 := 0) (f := f) hmono hbelow tendsto_leftTime
      (leftVertex_tendsto_ghost d hd h_missing z₀ hN₀)
      hleft_step_bound hleft_endpoint hleft_interpolation
  have hanchor_base : Continuous (fun P : ℝ ↦
      AffineMap.lineMap (negativeCoordinate d hd zLeft)
        (negativeCoordinate d hd z₀) (P + 1)) := by
    have harg : Continuous (fun P : ℝ ↦ P + 1) :=
      continuous_id.add continuous_const
    have hleft : Continuous (fun P : ℝ ↦
        (1 - (P + 1)) • negativeCoordinate d hd zLeft) :=
      (continuous_const.sub harg).smul continuous_const
    have hright : Continuous (fun P : ℝ ↦
        (P + 1) • negativeCoordinate d hd z₀) :=
      harg.smul continuous_const
    convert hleft.add hright using 1
    funext P
    rw [AffineMap.lineMap_apply_module]
    rfl
  have hanchor_cont : ContinuousOn f (Set.Icc (-1 : ℝ) 0) := by
    refine hanchor_base.continuousOn.congr ?_
    intro P hP
    dsimp [f]
    exact ghostCurveN_of_mem_Icc_neg_one_zero d hd h_missing zLeft z₀ h
      h_tendsto v P hP
  have hpast_base : Continuous (fun P : ℝ ↦
      (-P) • negativeCoordinate d hd zLeft) := by
    convert (continuous_id.neg.smul (continuous_const : Continuous (fun _ : ℝ ↦
      negativeCoordinate d hd zLeft))) using 1
    funext P
    rfl
  have hpast_cont : ContinuousOn f (Set.Iic (-1 : ℝ)) := by
    refine hpast_base.continuousOn.congr ?_
    intro P hP
    dsimp [f]
    exact ghostCurveN_of_le_neg_one d hd h_missing zLeft z₀ h h_tendsto v P hP
  have hrightStep : ∀ n : ℕ,
      DetectorTriple.rightTime (n + 1) < DetectorTriple.rightTime n := by
    intro n
    rw [← sub_pos, DetectorTriple.rightTime_sub_succ]
    positivity
  have hrightAnti : StrictAnti DetectorTriple.rightTime := by
    intro a b hab
    have hea : DetectorTriple.rightTime a = 2 - leftTime a := by
      rw [DetectorTriple.rightTime_def, leftTime_def]
      ring
    have heb : DetectorTriple.rightTime b = 2 - leftTime b := by
      rw [DetectorTriple.rightTime_def, leftTime_def]
      ring
    rw [hea, heb]
    have hleftStep : ∀ n : ℕ, leftTime n < leftTime (n + 1) := by
      intro n
      rw [← sub_pos, leftTime_succ_sub]
      positivity
    have hleftMono : StrictMono leftTime := strictMono_nat_of_lt_succ hleftStep
    linarith [hleftMono hab]
  have hrightAbove : ∀ n : ℕ, (1 : ℝ) < DetectorTriple.rightTime n := by
    intro n
    rw [DetectorTriple.rightTime_def]
    have hp : 0 < (2 : ℝ) ^ (-(n + 1 : ℝ)) := by positivity
    linarith
  have hrightTendsto :
      Filter.Tendsto DetectorTriple.rightTime Filter.atTop (nhds (1 : ℝ)) := by
    have heq : DetectorTriple.rightTime =
        (fun n : ℕ ↦ 2 - leftTime n) := by
      funext n
      rw [DetectorTriple.rightTime_def, leftTime_def]
      ring
    have hlim := (tendsto_const_nhds (x := (2 : ℝ))).sub tendsto_leftTime
    rw [heq]
    convert hlim using 1
    norm_num
  have hrightChain : LipschitzOnWith 1 f
      (Set.Icc (1 : ℝ) (DetectorTriple.rightTime 0)) := by
    have hright_step_bound : ∀ n : ℕ,
        ‖negativeCoordinate d hd
            (rightVertex d hd h_missing h h_tendsto (n + 1)) -
          negativeCoordinate d hd
            (rightVertex d hd h_missing h h_tendsto n)‖ ≤
          (1 : ℝ) * |DetectorTriple.rightTime (n + 1) -
            DetectorTriple.rightTime n| := by
      intro n
      have hs := rightVertex_slope_lt_one d hd h_missing h h_tendsto n
      have hgap : 0 < DetectorTriple.rightTime n -
          DetectorTriple.rightTime (n + 1) := by
        rw [DetectorTriple.rightTime_sub_succ]
        positivity
      calc
        ‖negativeCoordinate d hd
              (rightVertex d hd h_missing h h_tendsto (n + 1)) -
            negativeCoordinate d hd
              (rightVertex d hd h_missing h h_tendsto n)‖ =
            ‖negativeCoordinate d hd
                (rightVertex d hd h_missing h h_tendsto n) -
              negativeCoordinate d hd
                (rightVertex d hd h_missing h h_tendsto (n + 1))‖ :=
          norm_sub_rev _ _
        _ ≤ DetectorTriple.rightTime n - DetectorTriple.rightTime (n + 1) := hs.le
        _ = (1 : ℝ) * |DetectorTriple.rightTime (n + 1) -
            DetectorTriple.rightTime n| := by
          have hgap' : DetectorTriple.rightTime (n + 1) -
              DetectorTriple.rightTime n ≤ 0 := by linarith
          rw [abs_of_nonpos hgap']
          ring
    have hright_endpoint : f 1 = 0 := by
      dsimp [f]
      exact ghostCurveN_one d hd h_missing zLeft z₀ h h_tendsto v
    have hright_interpolation : ∀ n : ℕ, Set.EqOn f
        (fun s ↦ AffineMap.lineMap
          (negativeCoordinate d hd
            (rightVertex d hd h_missing h h_tendsto (n + 1)))
          (negativeCoordinate d hd
            (rightVertex d hd h_missing h h_tendsto n))
          ((s - DetectorTriple.rightTime (n + 1)) /
            (DetectorTriple.rightTime n - DetectorTriple.rightTime (n + 1))))
        (Set.Icc (DetectorTriple.rightTime (n + 1))
          (DetectorTriple.rightTime n)) := by
      intro n s hs
      dsimp [f]
      exact ghostCurveN_of_mem_Icc_rightTime d hd h_missing zLeft z₀ h h_tendsto v n s hs
    exact AffineMap.lipschitzOnWith_chainInterpolation_of_strictAnti
      (E := HilbertProd2 UnitL2) (K := (1 : NNReal)) (a := (1 : ℝ))
      (t := DetectorTriple.rightTime)
      (x := fun n ↦ negativeCoordinate d hd
        (rightVertex d hd h_missing h h_tendsto n))
      (x0 := 0) (f := f) hrightAnti hrightAbove hrightTendsto
      (rightVertex_tendsto_ghost d hd h_missing h h_tendsto)
      hright_step_bound hright_endpoint hright_interpolation
  have lineMap_continuous (u₀ u₁ : HilbertProd2 UnitL2) (a b : ℝ) :
      Continuous (fun P : ℝ ↦
        AffineMap.lineMap u₀ u₁ ((P - a) / (b - a))) := by
    have harg : Continuous (fun P : ℝ ↦ (P - a) / (b - a)) :=
      (continuous_id.sub continuous_const).div_const _
    have hleft : Continuous (fun P : ℝ ↦
        (1 - ((P - a) / (b - a))) • u₀) :=
      (continuous_const.sub harg).smul continuous_const
    have hright : Continuous (fun P : ℝ ↦
        ((P - a) / (b - a)) • u₁) :=
      harg.smul continuous_const
    convert hleft.add hright using 1
    funext P
    rw [AffineMap.lineMap_apply_module]
    rfl
  have hrt0 : DetectorTriple.rightTime 0 = (3 / 2 : ℝ) := by
    rw [DetectorTriple.rightTime_def]
    norm_num [Real.rpow_neg htwo_nonneg]
  have hbridge_cont : ContinuousOn f (Set.Icc (3 / 2 : ℝ) 2) := by
    have hline := lineMap_continuous
      (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0))
      (negativeCoordinate d hd ((2 : ℝ) • v)) (3 / 2 : ℝ) 2
    refine hline.continuousOn.congr ?_
    intro P hP
    have hP' : P ∈ Set.Icc (DetectorTriple.rightTime 0) 2 := by
      rw [hrt0]
      exact hP
    dsimp [f]
    simpa only [hrt0] using
      (ghostCurveN_of_mem_Icc_rightTime_zero_two d hd h_missing zLeft z₀ h h_tendsto v P hP')
  have hfuture_base : Continuous (fun P : ℝ ↦
      P • negativeCoordinate d hd v) := by
    exact continuous_id.smul continuous_const
  have hfuture_cont : ContinuousOn f (Set.Ici (2 : ℝ)) := by
    refine hfuture_base.continuousOn.congr ?_
    intro P hP
    dsimp [f]
    exact ghostCurveN_of_two_le d hd h_missing zLeft z₀ h h_tendsto v P hP
  have hleft_cont : ContinuousOn f (Set.Iic (1 : ℝ)) := by
    have hu₁ : ContinuousOn f (Set.Iic (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 0) :=
      hpast_cont.union_of_isClosed hanchor_cont isClosed_Iic isClosed_Icc
    have hu₂ : ContinuousOn f
        ((Set.Iic (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 0) ∪
          Set.Icc (0 : ℝ) (leftTime 0)) :=
      hu₁.union_of_isClosed hinit.continuousOn
        (isClosed_Iic.union isClosed_Icc) isClosed_Icc
    have hu₃ : ContinuousOn f
        (((Set.Iic (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 0) ∪
          Set.Icc (0 : ℝ) (leftTime 0)) ∪ Set.Icc (leftTime 0) 1) :=
      hu₂.union_of_isClosed hleftChain.continuousOn
        ((isClosed_Iic.union isClosed_Icc).union isClosed_Icc) isClosed_Icc
    apply hu₃.mono
    intro P hP
    by_cases h₁ : P ≤ (-1 : ℝ)
    · exact Or.inl (Or.inl (Or.inl h₁))
    · have h₁' : (-1 : ℝ) ≤ P := le_of_not_ge h₁
      by_cases h₂ : P ≤ 0
      · exact Or.inl (Or.inl (Or.inr ⟨h₁', h₂⟩))
      · have h₂' : (0 : ℝ) ≤ P := le_of_not_ge h₂
        by_cases h₃ : P ≤ leftTime 0
        · exact Or.inl (Or.inr ⟨h₂', h₃⟩)
        · exact Or.inr ⟨le_of_not_ge h₃, hP⟩
  have hbridge_cont' : ContinuousOn f
      (Set.Icc (DetectorTriple.rightTime 0) 2) := by
    rw [hrt0]
    exact hbridge_cont
  have hright_cont : ContinuousOn f (Set.Ici (1 : ℝ)) := by
    have hu₁ : ContinuousOn f
        (Set.Icc (1 : ℝ) (DetectorTriple.rightTime 0) ∪
          Set.Icc (DetectorTriple.rightTime 0) 2) :=
      hrightChain.continuousOn.union_of_isClosed hbridge_cont'
        isClosed_Icc isClosed_Icc
    have hu₂ : ContinuousOn f
        ((Set.Icc (1 : ℝ) (DetectorTriple.rightTime 0) ∪
          Set.Icc (DetectorTriple.rightTime 0) 2) ∪ Set.Ici (2 : ℝ)) :=
      hu₁.union_of_isClosed hfuture_cont
        (isClosed_Icc.union isClosed_Icc) isClosed_Ici
    apply hu₂.mono
    intro P hP
    by_cases h₁ : P ≤ DetectorTriple.rightTime 0
    · exact Or.inl (Or.inl ⟨hP, h₁⟩)
    · have h₁' : DetectorTriple.rightTime 0 ≤ P := le_of_not_ge h₁
      by_cases h₂ : P ≤ 2
      · exact Or.inl (Or.inr ⟨h₁', h₂⟩)
      · exact Or.inr (le_of_not_ge h₂)
  have hunion : ContinuousOn f (Set.Iic (1 : ℝ) ∪ Set.Ici (1 : ℝ)) :=
    hleft_cont.union_of_isClosed hright_cont isClosed_Iic isClosed_Ici
  have hcover : Set.Iic (1 : ℝ) ∪ Set.Ici (1 : ℝ) = Set.univ := by
    ext P
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
    exact le_total P 1
  rw [hcover] at hunion
  rw [← continuousOn_univ]
  exact hunion


end Lorentz
