module

public import ReasLib.Analysis.ChainInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Asymptotics
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Asymptotics
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay
public import ReasLib.Topology.MetricSpace.Lipschitz

public section

namespace Lorentz

/-- Adjacent closed intervals with a common endpoint inherit a uniform Lipschitz
bound.  This local companion keeps the ghost-curve assembly independent of the
private implementation details of `ChainInterpolation`. -/
private lemma lipschitzOnWith_Icc_union_adjacent_local
    {Y : Type*} [PseudoMetricSpace Y] (K : NNReal)
    {a b c : ℝ} {f : ℝ → Y} (hab : a ≤ b) (hbc : b ≤ c)
    (hleft : LipschitzOnWith K f (Set.Icc a b))
    (hright : LipschitzOnWith K f (Set.Icc b c)) :
    LipschitzOnWith K f (Set.Icc a c) := by
  have hordered : ∀ {x y : ℝ}, x ∈ Set.Icc a c → y ∈ Set.Icc a c → x ≤ y →
      dist (f x) (f y) ≤ (K : ℝ) * dist x y := by
    intro x y hx hy hxy
    by_cases hyb : y ≤ b
    · exact hleft.dist_le_mul x ⟨hx.1, hxy.trans hyb⟩ y ⟨hy.1, hyb⟩
    · have hby : b ≤ y := le_of_not_ge hyb
      by_cases hbx : b ≤ x
      · exact hright.dist_le_mul x ⟨hbx, hxy.trans hy.2⟩ y ⟨hby, hy.2⟩
      · have hxb : x ≤ b := le_of_not_ge hbx
        have h₁ := hleft.dist_le_mul x ⟨hx.1, hxb⟩ b ⟨hab, le_rfl⟩
        have h₂ := hright.dist_le_mul b ⟨le_rfl, hbc⟩ y ⟨hby, hy.2⟩
        calc
          dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) :=
            dist_triangle _ _ _
          _ ≤ (K : ℝ) * dist x b + (K : ℝ) * dist b y := add_le_add h₁ h₂
          _ = (K : ℝ) * dist x y := by
            simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxb),
              abs_of_nonpos (sub_nonpos.mpr hby),
              abs_of_nonpos (sub_nonpos.mpr hxy)]
            ring
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rcases le_total x y with hxy | hyx
  · exact hordered hx hy hxy
  · simpa only [dist_comm] using hordered hy hx hyx

/-- A Lipschitz bound on a left closed half-line and its adjacent finite interval
extends to the larger half-line. -/
private lemma lipschitzOnWith_Iic_union_local {Y : Type*} [PseudoMetricSpace Y]
    (K : NNReal) {a c : ℝ} {f : ℝ → Y} (hac : a ≤ c)
    (hleft : LipschitzOnWith K f (Set.Iic a))
    (hright : LipschitzOnWith K f (Set.Icc a c)) :
    LipschitzOnWith K f (Set.Iic c) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  by_cases hxa : x ≤ a
  · by_cases hya : y ≤ a
    · exact hleft.dist_le_mul x hxa y hya
    · have hay : a ≤ y := le_of_not_ge hya
      have h₁ := hleft.dist_le_mul x hxa a (show a ≤ a from le_rfl)
      have h₂ := hright.dist_le_mul a ⟨le_rfl, hac⟩ y ⟨hay, hy⟩
      calc
        dist (f x) (f y) ≤ dist (f x) (f a) + dist (f a) (f y) :=
          dist_triangle _ _ _
        _ ≤ (K : ℝ) * dist x a + (K : ℝ) * dist a y := add_le_add h₁ h₂
        _ = (K : ℝ) * dist x y := by
          simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxa),
            abs_of_nonpos (sub_nonpos.mpr hay),
            abs_of_nonpos (sub_nonpos.mpr (hxa.trans hay))]
          ring
  · have hax : a ≤ x := le_of_not_ge hxa
    by_cases hya : y ≤ a
    · have h₁ := hright.dist_le_mul a ⟨le_rfl, hac⟩ x ⟨hax, hx⟩
      have h₂ := hleft.dist_le_mul y hya a (show a ≤ a from le_rfl)
      rw [dist_comm (f x) (f y), dist_comm x y]
      calc
        dist (f y) (f x) ≤ dist (f y) (f a) + dist (f a) (f x) :=
          dist_triangle _ _ _
        _ ≤ (K : ℝ) * dist y a + (K : ℝ) * dist a x := add_le_add h₂ h₁
        _ = (K : ℝ) * dist y x := by
          simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hya),
            abs_of_nonpos (sub_nonpos.mpr hax),
            abs_of_nonpos (sub_nonpos.mpr (hya.trans hax))]
          ring
    · exact hright.dist_le_mul x ⟨hax, hx⟩ y ⟨le_of_not_ge hya, hy⟩

/-- A finite interval and a right closed half-line with a common endpoint inherit
a uniform Lipschitz bound. -/
private lemma lipschitzOnWith_Ici_union_local {Y : Type*} [PseudoMetricSpace Y]
    (K : NNReal) {a c : ℝ} {f : ℝ → Y} (hac : a ≤ c)
    (hleft : LipschitzOnWith K f (Set.Icc a c))
    (hright : LipschitzOnWith K f (Set.Ici c)) :
    LipschitzOnWith K f (Set.Ici a) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  by_cases hxc : c ≤ x
  · by_cases hyc : c ≤ y
    · exact hright.dist_le_mul x hxc y hyc
    · have hyc' : y ≤ c := le_of_not_ge hyc
      have h₁ := hright.dist_le_mul x hxc c (show c ≤ c from le_rfl)
      have h₂ := hleft.dist_le_mul c ⟨hac, le_rfl⟩ y ⟨hy, hyc'⟩
      calc
        dist (f x) (f y) ≤ dist (f x) (f c) + dist (f c) (f y) :=
          dist_triangle _ _ _
        _ ≤ (K : ℝ) * dist x c + (K : ℝ) * dist c y := add_le_add h₁ h₂
        _ = (K : ℝ) * dist x y := by
          simp only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxc),
            abs_of_nonneg (sub_nonneg.mpr hyc'),
            abs_of_nonneg (sub_nonneg.mpr (hyc'.trans hxc))]
          ring
  · have hxc' : x ≤ c := le_of_not_ge hxc
    by_cases hyc : c ≤ y
    · have h₁ := hleft.dist_le_mul x ⟨hx, hxc'⟩ c ⟨hac, le_rfl⟩
      have h₂ := hright.dist_le_mul c (show c ≤ c from le_rfl) y hyc
      calc
        dist (f x) (f y) ≤ dist (f x) (f c) + dist (f c) (f y) :=
          dist_triangle _ _ _
        _ ≤ (K : ℝ) * dist x c + (K : ℝ) * dist c y := add_le_add h₁ h₂
        _ = (K : ℝ) * dist x y := by
          simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxc'),
            abs_of_nonpos (sub_nonpos.mpr hyc),
            abs_of_nonpos (sub_nonpos.mpr (hxc'.trans hyc))]
          ring
    · exact hleft.dist_le_mul x ⟨hx, hxc'⟩ y ⟨hy, le_of_not_ge hyc⟩

/-- The negative-coordinate ghost curve is `1`-Lipschitz on the half-line through
the ghost time from the left. -/
theorem lipschitzOnWith_ghostCurveN_Iic (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (h_zLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (h_anchor : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (h_z₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) :
    LipschitzOnWith 1 (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
      (Set.Iic (1 : ℝ)) := by
  let f : ℝ → HilbertProd2 UnitL2 :=
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
  have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hneg_half_nonpos : (-(1 / 2 : ℝ)) ≤ 0 := by norm_num
  have ht0 : 0 < leftTime 0 := by
    rw [leftTime_def]
    norm_num [Real.rpow_neg htwo_nonneg]
  have htime0 : leftTime 0 = (1 / 2 : ℝ) := by
    rw [leftTime_def]
    norm_num [Real.rpow_neg htwo_nonneg]
  have hpast : LipschitzOnWith 1 f (Set.Iic (-1 : ℝ)) := by
    refine LipschitzOnWith.of_dist_le_mul fun P hP Q hQ ↦ ?_
    dsimp [f]
    rw [
      ghostCurveN_of_le_neg_one d hd h_missing zLeft z₀ h h_tendsto v P hP,
      ghostCurveN_of_le_neg_one d hd h_missing zLeft z₀ h h_tendsto v Q hQ]
    rw [dist_eq_norm, ← sub_smul]
    have hs : ‖negativeCoordinate d hd zLeft‖ ≤ 1 := by
      linarith
    calc
      ‖(-P - -Q) • negativeCoordinate d hd zLeft‖ =
          |P - Q| * ‖negativeCoordinate d hd zLeft‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
        ring
      _ ≤ |P - Q| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = (1 : ℝ) * dist P Q := by
        rw [Real.dist_eq]
        ring
  have hanchorL : LipschitzOnWith 1 f (Set.Icc (-1 : ℝ) 0) := by
    have hendpoint : ‖negativeCoordinate d hd z₀ - negativeCoordinate d hd zLeft‖ ≤
        (1 : ℝ) * (0 - (-1 : ℝ)) := by
      rw [norm_sub_rev]
      norm_num
      exact h_anchor.le
    have hneg_one_lt_zero : (-1 : ℝ) < 0 := by norm_num
    have hL := AffineMap.lipschitzOnWith_lineMap_interval
      (a := (-1 : ℝ)) (b := (0 : ℝ))
      (u := negativeCoordinate d hd zLeft) (v := negativeCoordinate d hd z₀)
      (K := (1 : NNReal)) hneg_one_lt_zero hendpoint
    have hL' : LipschitzOnWith 1
        (fun t : ℝ ↦ AffineMap.lineMap (negativeCoordinate d hd zLeft)
          (negativeCoordinate d hd z₀) (t + 1)) (Set.Icc (-1 : ℝ) 0) := by
      simpa [sub_neg_eq_add] using hL
    refine LipschitzOnWith.of_dist_le_mul fun P hP Q hQ ↦ ?_
    change dist (f P) (f Q) ≤ (1 : ℝ) * dist P Q
    dsimp [f]
    rw [
      ghostCurveN_of_mem_Icc_neg_one_zero d hd h_missing zLeft z₀ h h_tendsto v P hP,
      ghostCurveN_of_mem_Icc_neg_one_zero d hd h_missing zLeft z₀ h h_tendsto v Q hQ]
    exact hL'.dist_le_mul P hP Q hQ
  have hinitialL : LipschitzOnWith 1 f (Set.Icc (0 : ℝ) (leftTime 0)) := by
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
          negativeCoordinate d hd z₀ = -(1 / 2 : ℝ) •
            negativeCoordinate d hd z₀ := by
        module
      rw [hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos hneg_half_nonpos]
      nlinarith
    have hvertex' :
        ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
            leftTemplate (negativeCoordinate d hd z₀) (leftTime 0)‖ <
          (1 / 32 : ℝ) := by
      exact lt_of_lt_of_eq hvertex hrad
    have hend : ‖negativeCoordinate d hd
          (leftVertex d hd h_missing z₀ 0) - negativeCoordinate d hd z₀‖ <
        leftTime 0 := by
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
    have hend_le : ‖negativeCoordinate d hd
          (leftVertex d hd h_missing z₀ 0) - negativeCoordinate d hd z₀‖ ≤
        (1 : ℝ) * (leftTime 0 - 0) := by
      simpa only [sub_zero, one_mul] using hend.le
    have hL := AffineMap.lipschitzOnWith_lineMap_interval
      (a := (0 : ℝ)) (b := leftTime 0)
      (u := negativeCoordinate d hd z₀)
      (v := negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0))
      (K := (1 : NNReal)) ht0 hend_le
    refine LipschitzOnWith.of_dist_le_mul fun P hP Q hQ ↦ ?_
    change dist (f P) (f Q) ≤ (1 : ℝ) * dist P Q
    dsimp [f]
    rw [
      ghostCurveN_of_mem_Icc_zero_leftTime d hd h_missing zLeft z₀ h h_tendsto v P hP,
      ghostCurveN_of_mem_Icc_zero_leftTime d hd h_missing zLeft z₀ h h_tendsto v Q hQ]
    simpa only [sub_zero, NNReal.coe_one] using hL.dist_le_mul P hP Q hQ
  have hchainL : LipschitzOnWith 1 f (Set.Icc (leftTime 0) (1 : ℝ)) := by
    have hstep : ∀ n : ℕ, leftTime n < leftTime (n + 1) := by
      intro n
      rw [← sub_pos, leftTime_succ_sub]
      positivity
    have hmono : StrictMono leftTime := strictMono_nat_of_lt_succ hstep
    have hbelow : ∀ n : ℕ, leftTime n < (1 : ℝ) := by
      intro n
      rw [leftTime_def]
      have hp : 0 < (2 : ℝ) ^ (-(n + 1 : ℝ)) := by positivity
      linarith
    apply AffineMap.lipschitzOnWith_chainInterpolation_of_strictMono
      (K := (1 : NNReal)) (a := (1 : ℝ)) (t := leftTime)
      (x := fun n ↦ negativeCoordinate d hd
        (leftVertex d hd h_missing z₀ n)) (x0 := 0) (f := f)
    · exact hmono
    · exact hbelow
    · exact tendsto_leftTime
    · exact leftVertex_tendsto_ghost d hd h_missing z₀ h_z₀
    · intro n
      have hgap : 0 < leftTime (n + 1) - leftTime n := by
        rw [leftTime_succ_sub]
        positivity
      have hs := leftVertex_slope_lt_one d hd h_missing z₀ h_z₀ n
      simpa only [abs_of_pos hgap, NNReal.coe_one, one_mul] using hs.le
    · simpa only [f] using
        (ghostCurveN_one d hd h_missing zLeft z₀ h h_tendsto v)
    · intro n s hs
      simpa only [f] using
        (ghostCurveN_of_mem_Icc_leftTime d hd h_missing zLeft z₀ h h_tendsto v n s hs)
  have hzero_le_leftTime : (0 : ℝ) ≤ leftTime 0 := ht0.le
  have hleftTime_le_one : leftTime 0 ≤ (1 : ℝ) := by
    rw [htime0]
    norm_num
  have hminus_le_zero : (-1 : ℝ) ≤ 0 := by norm_num
  have hzero_le_one : (0 : ℝ) ≤ 1 := by norm_num
  have hminus_le_one : (-1 : ℝ) ≤ 1 := by norm_num
  have hzeroOne : LipschitzOnWith 1 f (Set.Icc (0 : ℝ) (1 : ℝ)) :=
    lipschitzOnWith_Icc_union_adjacent_local (K := (1 : NNReal))
      (a := (0 : ℝ)) (b := leftTime 0) (c := (1 : ℝ))
      hzero_le_leftTime hleftTime_le_one hinitialL hchainL
  have hminusOne : LipschitzOnWith 1 f (Set.Icc (-1 : ℝ) (1 : ℝ)) :=
    lipschitzOnWith_Icc_union_adjacent_local (K := (1 : NNReal))
      (a := (-1 : ℝ)) (b := (0 : ℝ)) (c := (1 : ℝ))
      hminus_le_zero hzero_le_one hanchorL hzeroOne
  have hleft : LipschitzOnWith 1 f (Set.Iic (1 : ℝ)) :=
    lipschitzOnWith_Iic_union_local (K := (1 : NNReal))
      (a := (-1 : ℝ)) (c := (1 : ℝ)) hminus_le_one hpast hminusOne
  simpa only [f] using hleft

/-- The negative-coordinate ghost curve is `1`-Lipschitz on the half-line through
the ghost time from the right. -/
theorem lipschitzOnWith_ghostCurveN_Ici (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (h_v : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16) :
    LipschitzOnWith 1 (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
      (Set.Ici (1 : ℝ)) := by
  let f : ℝ → HilbertProd2 UnitL2 :=
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
  have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hstep : ∀ n : ℕ,
      DetectorTriple.rightTime (n + 1) < DetectorTriple.rightTime n := by
    intro n
    rw [← sub_pos, DetectorTriple.rightTime_sub_succ]
    positivity
  have hanti : StrictAnti DetectorTriple.rightTime :=
    strictAnti_nat_of_succ_lt hstep
  have habove : ∀ n : ℕ, (1 : ℝ) < DetectorTriple.rightTime n := by
    intro n
    rw [DetectorTriple.rightTime_def]
    have hp : 0 < (2 : ℝ) ^ (-(n + 1 : ℝ)) := by positivity
    linarith
  have hrt_tendsto :
      Filter.Tendsto DetectorTriple.rightTime Filter.atTop (nhds (1 : ℝ)) := by
    have heq : (fun i : ℕ => DetectorTriple.rightTime i) =
        (fun i : ℕ => 2 - leftTime i) := by
      funext i
      rw [DetectorTriple.rightTime_def, leftTime_def]
      ring
    change Filter.Tendsto (fun i : ℕ => DetectorTriple.rightTime i)
      Filter.atTop (nhds (1 : ℝ))
    rw [heq]
    have h := (tendsto_const_nhds (x := (2 : ℝ))).sub tendsto_leftTime
    convert h using 1
    norm_num
  have hchainR : LipschitzOnWith 1 f
      (Set.Icc (1 : ℝ) (DetectorTriple.rightTime 0)) := by
    apply AffineMap.lipschitzOnWith_chainInterpolation_of_strictAnti
      (K := (1 : NNReal)) (a := (1 : ℝ))
      (t := DetectorTriple.rightTime)
      (x := fun n ↦ negativeCoordinate d hd
        (rightVertex d hd h_missing h h_tendsto n)) (x0 := 0) (f := f)
    · exact hanti
    · exact habove
    · exact hrt_tendsto
    · exact rightVertex_tendsto_ghost d hd h_missing h h_tendsto
    · intro n
      have hs := rightVertex_slope_lt_one d hd h_missing h h_tendsto n
      simpa only [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr (hstep n).le),
        NNReal.coe_one, one_mul, neg_sub] using hs.le
    · simpa only [f] using
        (ghostCurveN_one d hd h_missing zLeft z₀ h h_tendsto v)
    · intro n s hs
      simpa only [f] using
        (ghostCurveN_of_mem_Icc_rightTime d hd h_missing zLeft z₀ h h_tendsto v n s hs)
  have hrt0_eq : DetectorTriple.rightTime 0 = (3 / 2 : ℝ) := by
    rw [DetectorTriple.rightTime_def]
    norm_num [Real.rpow_neg htwo_nonneg]
  have houter : LipschitzOnWith 1 f
      (Set.Icc (DetectorTriple.rightTime 0) (2 : ℝ)) := by
    have hgap : 0 < (2 : ℝ) - DetectorTriple.rightTime 0 := by
      rw [hrt0_eq]
      norm_num
    have hbound := foldedToFuture_gap_lt_half d hd h_missing h h_tendsto v h_v
    have hendpoint :
        ‖negativeCoordinate d hd ((2 : ℝ) • v) -
            negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0)‖ ≤
          (1 : ℝ) * ((2 : ℝ) - DetectorTriple.rightTime 0) := by
      rw [norm_sub_rev]
      have hhalf : (2 : ℝ) - DetectorTriple.rightTime 0 = (1 / 2 : ℝ) := by
        rw [hrt0_eq]
        norm_num
      rw [hhalf]
      simpa only [one_mul] using hbound.le
    have hL := AffineMap.lipschitzOnWith_lineMap_interval
      (a := DetectorTriple.rightTime 0) (b := (2 : ℝ))
      (u := negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0))
      (v := negativeCoordinate d hd ((2 : ℝ) • v))
      (K := (1 : NNReal)) (sub_pos.mp hgap) hendpoint
    refine LipschitzOnWith.of_dist_le_mul fun P hP Q hQ ↦ ?_
    change dist (f P) (f Q) ≤ (1 : ℝ) * dist P Q
    dsimp [f]
    rw [
      ghostCurveN_of_mem_Icc_rightTime_zero_two d hd h_missing zLeft z₀ h h_tendsto v P hP,
      ghostCurveN_of_mem_Icc_rightTime_zero_two d hd h_missing zLeft z₀ h h_tendsto v Q hQ]
    simpa only [NNReal.coe_one, one_mul] using hL.dist_le_mul P hP Q hQ
  have hrt0_ge_one : (1 : ℝ) ≤ DetectorTriple.rightTime 0 :=
    (habove 0).le
  have hrt0_le_two : DetectorTriple.rightTime 0 ≤ (2 : ℝ) := by
    rw [hrt0_eq]
    norm_num
  have h_one_le_two : (1 : ℝ) ≤ 2 := by norm_num
  have hchainOuter : LipschitzOnWith 1 f (Set.Icc (1 : ℝ) (2 : ℝ)) :=
    lipschitzOnWith_Icc_union_adjacent_local (K := (1 : NNReal))
      (a := (1 : ℝ)) (b := DetectorTriple.rightTime 0) (c := (2 : ℝ))
      hrt0_ge_one hrt0_le_two hchainR houter
  have hfuture : LipschitzOnWith 1 f (Set.Ici (2 : ℝ)) := by
    refine LipschitzOnWith.of_dist_le_mul fun P hP Q hQ ↦ ?_
    rw [show f P = ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P by rfl,
      show f Q = ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v Q by rfl,
      ghostCurveN_of_two_le d hd h_missing zLeft z₀ h h_tendsto v P hP,
      ghostCurveN_of_two_le d hd h_missing zLeft z₀ h h_tendsto v Q hQ]
    rw [dist_eq_norm, ← sub_smul]
    have hs : ‖negativeCoordinate d hd v‖ ≤ 1 := by
      linarith
    calc
      ‖(P - Q) • negativeCoordinate d hd v‖ =
          |P - Q| * ‖negativeCoordinate d hd v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |P - Q| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = (1 : ℝ) * dist P Q := by
        rw [Real.dist_eq]
        ring
  have hIci : LipschitzOnWith 1 f (Set.Ici (1 : ℝ)) :=
    lipschitzOnWith_Ici_union_local (K := (1 : NNReal))
      (a := (1 : ℝ)) (c := (2 : ℝ)) h_one_le_two hchainOuter hfuture
  simpa only [f] using hIci

/-- Before the ghost time, the norm of the negative-coordinate ghost curve is
bounded by the distance to the ghost time. -/
theorem ghostCurveN_norm_le_one_sub (d : C0Seq) (hd : d ≠ 0)
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
    (P : ℝ) (hP : P < 1) :
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤ 1 - P := by
  have hPmem : P ∈ Set.Iic (1 : ℝ) := hP.le
  have h1mem : (1 : ℝ) ∈ Set.Iic (1 : ℝ) := by simp
  have hdist :=
    (lipschitzOnWith_ghostCurveN_Iic d hd h_missing zLeft z₀ h h_tendsto v
      h_zLeft h_anchor h_z₀).dist_le_mul P hPmem 1 h1mem
  simpa only [ghostCurveN_one, dist_zero_right, NNReal.coe_one, one_mul, Real.dist_eq,
    neg_sub,
    abs_of_nonpos (sub_nonpos.mpr hP.le)] using hdist

/-- After the ghost time, the norm of the negative-coordinate ghost curve is
bounded by the distance to the ghost time. -/
theorem ghostCurveN_norm_le_sub_one (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (h_v : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : 1 < P) :
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤ P - 1 := by
  have hPmem : P ∈ Set.Ici (1 : ℝ) := hP.le
  have h1mem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := by simp
  have hdist :=
    (lipschitzOnWith_ghostCurveN_Ici d hd h_missing zLeft z₀ h h_tendsto v
      h_v).dist_le_mul 1 h1mem P hPmem
  have hsimp :
      ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤ -(1 - P) := by
    simpa only [ghostCurveN_one, dist_zero_left, NNReal.coe_one, one_mul, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hP.le)] using hdist
  nlinarith

/-- Values of the negative-coordinate ghost curve at parameters on opposite sides
of the ghost time satisfy the triangle-inequality bound and its linear estimate. -/
theorem ghostCurveN_crossBounds (d : C0Seq) (hd : d ≠ 0)
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
    (h_v : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P Q : ℝ) (hP : P < 1) (hQ : 1 < Q) :
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v Q -
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤
      ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v Q‖ +
        ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ∧
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v Q‖ +
        ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤ Q - P := by
  constructor
  · exact norm_sub_le _ _
  · have hQbound := ghostCurveN_norm_le_sub_one d hd h_missing zLeft z₀ h h_tendsto v
      h_v Q hQ
    have hP' := ghostCurveN_norm_le_one_sub d hd h_missing zLeft z₀ h h_tendsto v
      h_zLeft h_anchor h_z₀ P hP
    linarith


/-- The negative-coordinate ghost curve is globally `1`-Lipschitz. -/
theorem lipschitzWith_ghostCurveN (d : C0Seq) (hd : d ≠ 0)
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
    LipschitzWith 1 (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v) := by
  apply LipschitzWith.of_iic_ici_of_norm_le (a := (1 : ℝ))
  · exact ghostCurveN_one d hd h_missing zLeft z₀ h h_tendsto v
  · exact lipschitzOnWith_ghostCurveN_Iic d hd h_missing zLeft z₀ h h_tendsto v
      h_zLeft h_anchor h_z₀
  · exact lipschitzOnWith_ghostCurveN_Ici d hd h_missing zLeft z₀ h h_tendsto v h_v
  · intro P
    by_cases hP : P < 1
    · have hbound := ghostCurveN_norm_le_one_sub d hd h_missing zLeft z₀ h h_tendsto v
        h_zLeft h_anchor h_z₀ P hP
      rw [abs_of_nonpos (sub_nonpos.mpr hP.le)]
      simpa only [NNReal.coe_one, one_mul, neg_sub] using hbound
    · by_cases hEq : P = 1
      · subst P
        simp only [ghostCurveN_one, norm_zero, sub_self, abs_zero, NNReal.coe_one,
          mul_zero, le_refl]
      · have hP' : 1 < P := lt_of_le_of_ne (le_of_not_gt hP) (Ne.symm hEq)
        have hbound := ghostCurveN_norm_le_sub_one d hd h_missing zLeft z₀ h h_tendsto v
          h_v P hP'
        rw [abs_of_nonneg (sub_nonneg.mpr hP'.le)]
        simpa only [NNReal.coe_one, one_mul] using hbound

end Lorentz
