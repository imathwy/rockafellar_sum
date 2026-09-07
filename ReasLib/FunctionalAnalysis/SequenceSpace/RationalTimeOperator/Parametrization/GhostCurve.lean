module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Order.Lattice.Nat
public import ReasLib.Analysis.DyadicDetectorSchedule
public import ReasLib.Analysis.LeftDyadicTemplate
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates

public section

namespace Lorentz

/-- The index of the left dyadic edge containing a parameter below the ghost time. -/
noncomputable def leftEdgeIndex (P : ℝ) : ℕ :=
  sInf {k : ℕ | P ≤ leftTime (k + 1)}

/-- The selected left edge has `P` between its two consecutive dyadic times. -/
theorem leftEdgeIndex_spec (P : ℝ) (hP₀ : leftTime 0 < P) (hP₁ : P < 1) :
    leftTime (leftEdgeIndex P) < P ∧ P ≤ leftTime (leftEdgeIndex P + 1) := by
  let S : Set ℕ := {k : ℕ | P ≤ leftTime (k + 1)}
  have hSev : ∀ᶠ n : ℕ in Filter.atTop, P < leftTime n := by
    exact (tendsto_order.1 tendsto_leftTime).1 P hP₁
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hSev)
  have hSne : S.Nonempty := by
    refine ⟨N, ?_⟩
    exact (hN (N + 1) (Nat.le_succ N)).le
  have hmem : leftEdgeIndex P ∈ S := by
    rw [show leftEdgeIndex P = sInf S by rfl]
    exact Nat.sInf_mem hSne
  have hupper : P ≤ leftTime (leftEdgeIndex P + 1) := hmem
  have hlower : leftTime (leftEdgeIndex P) < P := by
    by_cases hj : leftEdgeIndex P = 0
    · simpa [hj] using hP₀
    · have hjlt : (leftEdgeIndex P).pred < leftEdgeIndex P := Nat.pred_lt hj
      have hpred_not : (leftEdgeIndex P).pred ∉ S := by
        exact Nat.notMem_of_lt_sInf hjlt
      have hnot : ¬ P ≤ leftTime (leftEdgeIndex P) := by
        intro hle
        apply hpred_not
        have heq : (leftEdgeIndex P).pred + 1 = leftEdgeIndex P := by
          rw [Nat.pred_eq_sub_one]
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)
        change P ≤ leftTime ((leftEdgeIndex P).pred + 1)
        rw [heq]
        exact hle
      exact lt_of_not_ge hnot
  exact ⟨hlower, hupper⟩

/-- The index of the reversed right dyadic edge containing a parameter above the ghost time. -/
noncomputable def rightEdgeIndex (P : ℝ) : ℕ :=
  sInf {i : ℕ | DetectorTriple.rightTime (i + 1) ≤ P}

/-- The selected right edge has `P` between its two consecutive dyadic times. -/
theorem rightEdgeIndex_spec (P : ℝ) (hP₁ : 1 < P)
    (hP₀ : P ≤ DetectorTriple.rightTime 0) :
    DetectorTriple.rightTime (rightEdgeIndex P + 1) ≤ P ∧
      P ≤ DetectorTriple.rightTime (rightEdgeIndex P) := by
  let S : Set ℕ := {i : ℕ | DetectorTriple.rightTime (i + 1) ≤ P}
  have hrt_tendsto : Filter.Tendsto DetectorTriple.rightTime Filter.atTop (nhds 1) := by
    have heq : (fun i : ℕ => DetectorTriple.rightTime i) = fun i => 2 - leftTime i := by
      funext i
      rw [DetectorTriple.rightTime_def, leftTime_def]
      ring
    change Filter.Tendsto (fun i : ℕ => DetectorTriple.rightTime i) Filter.atTop (nhds 1)
    rw [heq]
    have h := (tendsto_const_nhds (x := (2 : ℝ))).sub tendsto_leftTime
    convert h using 1
    norm_num
  have hSev : ∀ᶠ n : ℕ in Filter.atTop, DetectorTriple.rightTime n < P := by
    exact (tendsto_order.1 hrt_tendsto).2 P hP₁
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hSev)
  have hSne : S.Nonempty := by
    refine ⟨N, ?_⟩
    exact (hN (N + 1) (Nat.le_succ N)).le
  have hmem : rightEdgeIndex P ∈ S := by
    rw [show rightEdgeIndex P = sInf S by rfl]
    exact Nat.sInf_mem hSne
  have hlower : DetectorTriple.rightTime (rightEdgeIndex P + 1) ≤ P := hmem
  have hupper : P ≤ DetectorTriple.rightTime (rightEdgeIndex P) := by
    by_cases hj : rightEdgeIndex P = 0
    · simpa [hj] using hP₀
    · have hjlt : (rightEdgeIndex P).pred < rightEdgeIndex P := Nat.pred_lt hj
      have hpred_not : (rightEdgeIndex P).pred ∉ S := by
        exact Nat.notMem_of_lt_sInf hjlt
      have hnot : ¬ DetectorTriple.rightTime (rightEdgeIndex P) ≤ P := by
        intro hle
        apply hpred_not
        have heq : (rightEdgeIndex P).pred + 1 = rightEdgeIndex P := by
          rw [Nat.pred_eq_sub_one]
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)
        change DetectorTriple.rightTime ((rightEdgeIndex P).pred + 1) ≤ P
        rw [heq]
        exact hle
      exact le_of_not_ge hnot
  exact ⟨hlower, hupper⟩

/-- The total negative-coordinate curve formed from the past and future rays,
the affine bridge and dyadic edges on each side, and the ghost value `0` at `P = 1`. -/
noncomputable def ghostCurveN (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (P : ℝ) : HilbertProd2 UnitL2 :=
  if P ≤ -1 then
    (-P) • negativeCoordinate d hd zLeft
  else if P ≤ 0 then
    AffineMap.lineMap (negativeCoordinate d hd zLeft) (negativeCoordinate d hd z₀) (P + 1)
  else if P < 1 then
    if P ≤ leftTime 0 then
      AffineMap.lineMap (negativeCoordinate d hd z₀)
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0))
        (P / leftTime 0)
    else
      let k := leftEdgeIndex P
      AffineMap.lineMap
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ k))
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ (k + 1)))
        ((P - leftTime k) / (leftTime (k + 1) - leftTime k))
  else if P = 1 then
    0
  else if P ≤ DetectorTriple.rightTime 0 then
    let i := rightEdgeIndex P
    AffineMap.lineMap
      (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1)))
      (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i))
      ((P - DetectorTriple.rightTime (i + 1)) /
        (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1)))
  else if P ≤ 2 then
    AffineMap.lineMap
      (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0))
      (negativeCoordinate d hd ((2 : ℝ) • v))
      ((P - DetectorTriple.rightTime 0) / (2 - DetectorTriple.rightTime 0))
  else
    P • negativeCoordinate d hd v

variable (d : C0Seq) (hd : d ≠ 0)
variable (h_missing : d ∉ Set.range L1Seq.positiveOperator)
variable (zLeft z₀ : parametrizedSubspace d)
variable (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
variable (h_tendsto : ∀ p q (h_pq : p < q),
  Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
    Filter.atTop (nhds 0))
variable (v : parametrizedSubspace d)

/-- On the past ray, the curve is the scaled negative coordinate of `zLeft`. -/
@[simp]
theorem ghostCurveN_of_le_neg_one (P : ℝ) (hP : P ≤ -1) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P =
      (-P) • negativeCoordinate d hd zLeft := by
  unfold ghostCurveN
  simp [hP]

/-- On `Set.Icc (-1) 0`, the curve is the affine edge from `zLeft` to `z₀`. -/
@[simp]
theorem ghostCurveN_of_mem_Icc_neg_one_zero (P : ℝ)
    (hP : P ∈ Set.Icc (-1 : ℝ) 0) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P =
      AffineMap.lineMap (negativeCoordinate d hd zLeft)
        (negativeCoordinate d hd z₀) (P + 1) := by
  unfold ghostCurveN
  by_cases hminus : P = -1
  · subst P
    simp
  · have hneg : ¬ P ≤ -1 := by
      intro hle
      exact hminus (le_antisymm hle hP.1)
    simp [hneg, hP.2]

/-- On the initial left interval, the curve joins `z₀` to the first left vertex. -/
@[simp]
theorem ghostCurveN_of_mem_Icc_zero_leftTime (P : ℝ)
    (hP : P ∈ Set.Icc (0 : ℝ) (leftTime 0)) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P =
      AffineMap.lineMap (negativeCoordinate d hd z₀)
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0))
        (P / leftTime 0) := by
  unfold ghostCurveN
  have hlt : P < 1 := by
    have htime : leftTime 0 < 1 := by
      rw [leftTime_def]
      norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [hP.2]
  have hneg : ¬ P ≤ -1 := by linarith [hP.1]
  by_cases hzero : P = 0
  · subst P
    simp [hneg]
  · have hPpos : 0 < P := lt_of_le_of_ne hP.1 (Ne.symm hzero)
    have hPnot : ¬ P ≤ 0 := not_le.mpr hPpos
    have houter : P ≤ leftTime 0 := hP.2
    simp [hneg, hPnot, hlt, houter]

/-- On a left dyadic interval, the curve joins the corresponding consecutive vertices. -/
@[simp]
theorem ghostCurveN_of_mem_Icc_leftTime (k : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (leftTime k) (leftTime (k + 1))) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P =
      AffineMap.lineMap
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ k))
        (negativeCoordinate d hd (leftVertex d hd h_missing z₀ (k + 1)))
        ((P - leftTime k) / (leftTime (k + 1) - leftTime k)) := by
  have hstep : ∀ n : ℕ, leftTime n < leftTime (n + 1) := by
    intro n
    rw [← sub_pos, leftTime_succ_sub]
    positivity
  have hmono : StrictMono leftTime := strictMono_nat_of_lt_succ hstep
  have hleftpos : ∀ n : ℕ, 0 < leftTime n := by
    intro n
    rw [leftTime_def]
    have hp : (2 : ℝ) ^ (-(n + 1 : ℝ)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · norm_num
      · norm_num [Nat.cast_add, Nat.cast_one]
        linarith
    linarith
  have hleftlt : ∀ n : ℕ, leftTime n < 1 := by
    intro n
    rw [leftTime_def]
    have hp : 0 < (2 : ℝ) ^ (-(n + 1 : ℝ)) := by positivity
    linarith
  have hPone : P < 1 := lt_of_le_of_lt hP.2 (hleftlt (k + 1))
  have hPpos : 0 < P := lt_of_lt_of_le (hleftpos k) hP.1
  have hnotneg : ¬ P ≤ (-1 : ℝ) := by linarith
  have hnotzero : ¬ P ≤ 0 := not_le.mpr hPpos
  by_cases hk0 : k = 0
  · subst k
    by_cases heq : P = leftTime 0
    · subst P
      rw [ghostCurveN_of_mem_Icc_zero_leftTime d hd h_missing zLeft z₀ h h_tendsto v
        (leftTime 0) ⟨(hleftpos 0).le, le_rfl⟩]
      have htime0 : leftTime 0 ≠ 0 := ne_of_gt (hleftpos 0)
      simp [htime0]
    · have hgt : leftTime 0 < P := lt_of_le_of_ne hP.1 (Ne.symm heq)
      have hidx0 : leftEdgeIndex P = 0 := by
        have hmem : (0 : ℕ) ∈ {j : ℕ | P ≤ leftTime (j + 1)} := hP.2
        have hle : leftEdgeIndex P ≤ 0 := by
          rw [leftEdgeIndex]
          exact Nat.sInf_le hmem
        exact Nat.eq_zero_of_le_zero hle
      have hnotouter : ¬ P ≤ leftTime 0 := not_le.mpr hgt
      unfold ghostCurveN
      rw [if_neg hnotneg, if_neg hnotzero, if_pos hPone, if_neg hnotouter]
      rw [hidx0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hleft0_lt : leftTime 0 < leftTime k := hmono (Nat.zero_lt_of_lt hkpos)
    have hleft0P : leftTime 0 < P := lt_of_lt_of_le hleft0_lt hP.1
    have hnotouter : ¬ P ≤ leftTime 0 := not_le.mpr hleft0P
    by_cases heq : P = leftTime k
    · subst P
      have hpred_succ : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
      have hmem : k - 1 ∈ {j : ℕ | leftTime k ≤ leftTime (j + 1)} := by
        change leftTime k ≤ leftTime (k - 1 + 1)
        rw [hpred_succ]
      have hidxmem : leftEdgeIndex (leftTime k) ∈
          {j : ℕ | leftTime k ≤ leftTime (j + 1)} := by
        rw [leftEdgeIndex]
        exact Nat.sInf_mem ⟨k - 1, hmem⟩
      have hidx_le : leftEdgeIndex (leftTime k) ≤ k - 1 := by
        rw [leftEdgeIndex]
        exact Nat.sInf_le hmem
      have hpred_le : k - 1 ≤ leftEdgeIndex (leftTime k) := by
        by_contra hnot
        have hlt : leftEdgeIndex (leftTime k) < k - 1 := Nat.lt_of_not_ge hnot
        have hsucc_lt : leftEdgeIndex (leftTime k) + 1 < k := by omega
        have htime_lt := hmono hsucc_lt
        have hmemle : leftTime k ≤ leftTime (leftEdgeIndex (leftTime k) + 1) := hidxmem
        exact (not_lt_of_ge hmemle) (lt_of_lt_of_le htime_lt (le_rfl))
      have hidx : leftEdgeIndex (leftTime k) = k - 1 := le_antisymm hidx_le hpred_le
      unfold ghostCurveN
      rw [if_neg hnotneg, if_neg hnotzero, if_pos hPone, if_neg hnotouter]
      rw [hidx]
      dsimp
      rw [hpred_succ]
      have hgap_prev : leftTime k - leftTime (k - 1) ≠ 0 := by
        have hprev : leftTime (k - 1) < leftTime k := by
          rw [← hpred_succ]
          exact hstep (k - 1)
        linarith
      simp [hgap_prev]
    · have hgt : leftTime k < P := lt_of_le_of_ne hP.1 (Ne.symm heq)
      have hmem : k ∈ {j : ℕ | P ≤ leftTime (j + 1)} := hP.2
      have hidxmem : leftEdgeIndex P ∈ {j : ℕ | P ≤ leftTime (j + 1)} := by
        rw [leftEdgeIndex]
        exact Nat.sInf_mem ⟨k, hmem⟩
      have hidx_le : leftEdgeIndex P ≤ k := by
        rw [leftEdgeIndex]
        exact Nat.sInf_le hmem
      have hk_le : k ≤ leftEdgeIndex P := by
        by_contra hnot
        have hsucc_le : leftEdgeIndex P + 1 ≤ k := by omega
        have htime_le := hmono.monotone hsucc_le
        have hmemle : P ≤ leftTime (leftEdgeIndex P + 1) := hidxmem
        exact (not_lt_of_ge (le_trans hmemle htime_le)) hgt
      have hidx : leftEdgeIndex P = k := le_antisymm hidx_le hk_le
      unfold ghostCurveN
      rw [if_neg hnotneg, if_neg hnotzero, if_pos hPone, if_neg hnotouter]
      rw [hidx]

/-- At the ghost time, the total curve has the prescribed missing value `0`. -/
@[simp]
theorem ghostCurveN_one :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 1 = 0 := by
  unfold ghostCurveN
  norm_num

/-- On a reversed right dyadic interval, the curve joins consecutive folded vertices. -/
@[simp]
theorem ghostCurveN_of_mem_Icc_rightTime (i : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (DetectorTriple.rightTime (i + 1))
      (DetectorTriple.rightTime i)) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P =
      AffineMap.lineMap
        (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1)))
        (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i))
        ((P - DetectorTriple.rightTime (i + 1)) /
          (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1))) := by
  have hleftstep : ∀ n : ℕ, leftTime n < leftTime (n + 1) := by
    intro n
    rw [← sub_pos, leftTime_succ_sub]
    positivity
  have hleftmono : StrictMono leftTime := strictMono_nat_of_lt_succ hleftstep
  have hrightstep : ∀ n : ℕ,
      DetectorTriple.rightTime (n + 1) < DetectorTriple.rightTime n := by
    intro n
    rw [← sub_pos, DetectorTriple.rightTime_sub_succ]
    positivity
  have hrightanti : StrictAnti DetectorTriple.rightTime := by
    intro a b hab
    have hea : DetectorTriple.rightTime a = 2 - leftTime a := by
      rw [DetectorTriple.rightTime_def, leftTime_def]
      ring
    have heb : DetectorTriple.rightTime b = 2 - leftTime b := by
      rw [DetectorTriple.rightTime_def, leftTime_def]
      ring
    rw [hea, heb]
    linarith [hleftmono hab]
  have hrt_gt_one : ∀ n : ℕ, (1 : ℝ) < DetectorTriple.rightTime n := by
    intro n
    rw [DetectorTriple.rightTime_def]
    have hp : 0 < (2 : ℝ) ^ (-(n + 1 : ℝ)) := by positivity
    linarith
  have hPone : 1 < P := lt_of_lt_of_le (hrt_gt_one (i + 1)) hP.1
  have hrt0mono : DetectorTriple.rightTime i ≤ DetectorTriple.rightTime 0 := by
    by_cases hi : i = 0
    · simp [hi]
    · have hi0 : 0 < i := Nat.pos_of_ne_zero hi
      have hlt := hrightanti hi0
      exact hlt.le
  have hP0 : P ≤ DetectorTriple.rightTime 0 := hP.2.trans hrt0mono
  let j := rightEdgeIndex P
  have hjmem : j ∈ {n : ℕ | DetectorTriple.rightTime (n + 1) ≤ P} := by
    dsimp [j]
    exact (rightEdgeIndex_spec P hPone hP0).1
  have hjupper : P ≤ DetectorTriple.rightTime j := by
    dsimp [j]
    exact (rightEdgeIndex_spec P hPone hP0).2
  have hile_mem : i ∈ {n : ℕ | DetectorTriple.rightTime (n + 1) ≤ P} := hP.1
  have hjle : j ≤ i := by
    dsimp [j]
    rw [rightEdgeIndex]
    exact Nat.sInf_le hile_mem
  have hige : i ≤ j + 1 := by
    by_contra hnot
    have hlt : j + 1 < i := Nat.lt_of_not_ge hnot
    have hrtlt := hrightanti hlt
    have hcontr : DetectorTriple.rightTime i < P :=
      lt_of_lt_of_le hrtlt hjmem
    exact (not_lt_of_ge hP.2) hcontr
  have hcases : j = i ∨ j + 1 = i := by omega
  have hneg : ¬ P ≤ (-1 : ℝ) := by linarith
  have hzero : ¬ P ≤ (0 : ℝ) := by linarith
  have hlt : ¬ P < (1 : ℝ) := by linarith
  have honeq : ¬ P = (1 : ℝ) := by linarith
  rcases hcases with hji | hsucc
  · have hidx : rightEdgeIndex P = i := by exact hji
    unfold ghostCurveN
    rw [if_neg hneg, if_neg hzero, if_neg hlt, if_neg honeq, if_pos hP0]
    change rightEdgeIndex P = i at hidx
    rw [hidx]
  · have hPeq : P = DetectorTriple.rightTime i := by
      have hlo : DetectorTriple.rightTime i ≤ P := by
        simpa [hsucc] using hjmem
      exact le_antisymm hP.2 hlo
    have hidx : rightEdgeIndex P + 1 = i := by exact hsucc
    unfold ghostCurveN
    rw [if_neg hneg, if_neg hzero, if_neg hlt, if_neg honeq, if_pos hP0]
    have hden_cur : DetectorTriple.rightTime i -
        DetectorTriple.rightTime (i + 1) ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (hrightstep i))
    have hidxsub : rightEdgeIndex P = i - 1 := by omega
    rw [hidxsub, hPeq]
    dsimp
    rw [show i - 1 + 1 = i by omega]
    simp [hden_cur]

/-- On the outer right bridge, the curve joins the first folded vertex to `2 • v`. -/
@[simp]
theorem ghostCurveN_of_mem_Icc_rightTime_zero_two (P : ℝ)
    (hP : P ∈ Set.Icc (DetectorTriple.rightTime 0) 2) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P =
      AffineMap.lineMap
        (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0))
        (negativeCoordinate d hd ((2 : ℝ) • v))
        ((P - DetectorTriple.rightTime 0) / (2 - DetectorTriple.rightTime 0)) := by
  have hrt0 : (1 : ℝ) < DetectorTriple.rightTime 0 := by
    rw [DetectorTriple.rightTime_def]
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have htwo : P ≤ (2 : ℝ) := hP.2
  have hneg : ¬ P ≤ (-1 : ℝ) := by linarith [hP.1, hrt0]
  have hzero : ¬ P ≤ (0 : ℝ) := by linarith [hP.1, hrt0]
  have hone : ¬ P < (1 : ℝ) := by linarith [hP.1, hrt0]
  have honeeq : ¬ P = (1 : ℝ) := by linarith [hP.1, hrt0]
  by_cases heq : P = DetectorTriple.rightTime 0
  · subst P
    have hPint : DetectorTriple.rightTime 0 ∈
        Set.Icc (DetectorTriple.rightTime (0 + 1)) (DetectorTriple.rightTime 0) := by
      constructor
      · rw [← sub_nonneg, DetectorTriple.rightTime_sub_succ]
        positivity
      · exact le_rfl
    rw [ghostCurveN_of_mem_Icc_rightTime d hd h_missing zLeft z₀ h h_tendsto v 0
      (DetectorTriple.rightTime 0) hPint]
    have hratio : (DetectorTriple.rightTime 0 - DetectorTriple.rightTime 0) /
        (2 - DetectorTriple.rightTime 0) = (0 : ℝ) := by simp
    have hgap : (DetectorTriple.rightTime 0 - DetectorTriple.rightTime (0 + 1)) /
        (DetectorTriple.rightTime 0 - DetectorTriple.rightTime (0 + 1)) = (1 : ℝ) := by
      apply div_self
      rw [DetectorTriple.rightTime_sub_succ]
      positivity
    rw [hgap, AffineMap.lineMap_apply_one, hratio, AffineMap.lineMap_apply_zero]
  · have hgt : DetectorTriple.rightTime 0 < P :=
      lt_of_le_of_ne hP.1 (Ne.symm heq)
    have hright : ¬ P ≤ DetectorTriple.rightTime 0 := not_le.mpr hgt
    unfold ghostCurveN
    rw [if_neg hneg, if_neg hzero, if_neg hone, if_neg honeeq, if_neg hright, if_pos htwo]

/-- On the future ray, the curve is the scaled negative coordinate of `v`. -/
@[simp]
theorem ghostCurveN_of_two_le (P : ℝ) (hP : 2 ≤ P) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P =
      P • negativeCoordinate d hd v := by
  unfold ghostCurveN
  by_cases hP2 : P = 2
  · subst P
    have hrt : ¬ (2 : ℝ) ≤ DetectorTriple.rightTime 0 := by
      rw [DetectorTriple.rightTime_def]
      norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hneg : ¬ (2 : ℝ) ≤ -1 := by norm_num
    have hzero : ¬ (2 : ℝ) ≤ 0 := by norm_num
    have hone : ¬ (2 : ℝ) < 1 := by norm_num
    have honeeq : ¬ (2 : ℝ) = 1 := by norm_num
    rw [if_neg hneg, if_neg hzero, if_neg hone, if_neg honeeq, if_neg hrt,
      if_pos (le_refl (2 : ℝ))]
    have hden : (2 - DetectorTriple.rightTime 0) /
        (2 - DetectorTriple.rightTime 0) = (1 : ℝ) := by
      apply div_self
      intro heq
      have hrt2 : DetectorTriple.rightTime 0 = 2 := by linarith
      rw [DetectorTriple.rightTime_def] at hrt2
      norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hrt2
    rw [hden, AffineMap.lineMap_apply_one, map_smul]
  · have hP2' : 2 < P := lt_of_le_of_ne hP (fun h => hP2 h.symm)
    have hneg : ¬ P ≤ -1 := by linarith
    have hzero : ¬ P ≤ 0 := by linarith
    have hone : ¬ P < 1 := by linarith
    have honeeq : ¬ P = 1 := by linarith
    have hrt : ¬ P ≤ DetectorTriple.rightTime 0 := by
      rw [DetectorTriple.rightTime_def]
      norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    have htwo : ¬ P ≤ 2 := by linarith
    simp [hneg, hzero, hone, honeeq, hrt, htwo]

/-- The curve takes the left-anchor value at `P = -1`. -/
@[simp]
theorem ghostCurveN_neg_one :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v (-1) =
      negativeCoordinate d hd zLeft := by
  unfold ghostCurveN
  simp

/-- The curve takes the time-zero anchor value at `P = 0`. -/
@[simp]
theorem ghostCurveN_zero :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 0 =
      negativeCoordinate d hd z₀ := by
  unfold ghostCurveN
  simp

/-- The curve takes the selected left-vertex value at every left dyadic time. -/
@[simp]
theorem ghostCurveN_leftTime (k : ℕ) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v (leftTime k) =
      negativeCoordinate d hd (leftVertex d hd h_missing z₀ k) := by
  have hleft : leftTime k ≤ leftTime (k + 1) := by
    rw [← sub_nonneg]
    rw [leftTime_succ_sub]
    positivity
  have hP : leftTime k ∈ Set.Icc (leftTime k) (leftTime (k + 1)) :=
    ⟨le_rfl, hleft⟩
  rw [ghostCurveN_of_mem_Icc_leftTime d hd h_missing zLeft z₀ h h_tendsto v k
    (leftTime k) hP]
  simp

/-- The curve takes the selected folded-vertex value at every right dyadic time. -/
@[simp]
theorem ghostCurveN_rightTime (i : ℕ) :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (DetectorTriple.rightTime i) =
      negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) := by
  have hright : DetectorTriple.rightTime (i + 1) ≤ DetectorTriple.rightTime i := by
    rw [← sub_nonneg]
    rw [DetectorTriple.rightTime_sub_succ]
    positivity
  have hP : DetectorTriple.rightTime i ∈
      Set.Icc (DetectorTriple.rightTime (i + 1)) (DetectorTriple.rightTime i) :=
    ⟨hright, le_rfl⟩
  rw [ghostCurveN_of_mem_Icc_rightTime d hd h_missing zLeft z₀ h h_tendsto v i
    (DetectorTriple.rightTime i) hP]
  have hden : (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1)) /
      (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1)) = (1 : ℝ) := by
    apply div_self
    rw [DetectorTriple.rightTime_sub_succ]
    positivity
  rw [hden, AffineMap.lineMap_apply_one]

/-- At `P = 3 / 2`, the curve is at the outermost folded vertex. -/
@[simp]
theorem ghostCurveN_three_halves :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v (3 / 2 : ℝ) =
      negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) := by
  have hrt : DetectorTriple.rightTime 0 = (3 / 2 : ℝ) := by
    rw [DetectorTriple.rightTime_def]
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← hrt]
  exact ghostCurveN_rightTime d hd h_missing zLeft z₀ h h_tendsto v 0

/-- At `P = 2`, the curve agrees with the endpoint of the future ray. -/
@[simp]
theorem ghostCurveN_two :
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 2 =
      (2 : ℝ) • negativeCoordinate d hd v := by
  unfold ghostCurveN
  have hrt : ¬ (2 : ℝ) ≤ DetectorTriple.rightTime 0 := by
    rw [DetectorTriple.rightTime_def]
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hneg : ¬ (2 : ℝ) ≤ -1 := by norm_num
  have hzero : ¬ (2 : ℝ) ≤ 0 := by norm_num
  have hone : ¬ (2 : ℝ) < 1 := by norm_num
  have honeeq : ¬ (2 : ℝ) = 1 := by norm_num
  rw [if_neg hneg, if_neg hzero, if_neg hone, if_neg honeeq, if_neg hrt,
    if_pos (le_refl (2 : ℝ))]
  have hden : (2 - DetectorTriple.rightTime 0) /
      (2 - DetectorTriple.rightTime 0) = (1 : ℝ) := by
    apply div_self
    intro heq
    have hrt2 : DetectorTriple.rightTime 0 = 2 := by linarith
    rw [DetectorTriple.rightTime_def] at hrt2
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hrt2
  rw [hden, AffineMap.lineMap_apply_one, map_smul]

end Lorentz
