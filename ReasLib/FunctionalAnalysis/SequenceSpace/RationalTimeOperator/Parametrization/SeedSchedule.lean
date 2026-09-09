/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedBase
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.ScaledDetector
public import ReasLib.Data.Countable.RepeatingSchedule
public import ReasLib.FunctionalAnalysis.DualPairing.Monotone

/-!
# Fixed signed schedule for the S3 seed

Natural index n represents source index n + 1. The signed coordinate label
(q, b) represents coordinate q + 2 and sign determined by b.
-/

public section

open Filter Topology
open scoped InnerProductSpace

namespace Lorentz

/-- Unit differences of arbitrarily small interval norm can be placed beyond
any finite prefix. -/
theorem exists_remote_unitDifference_norm_lt (q N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ j, N < j ∧ ‖L1Seq.intervalCoordinateOperator (unitDifference q j)‖ < ε := by
  obtain ⟨φ, hφ, ht⟩ := exists_strictMono_rationalTime_tendsto (rationalTime q)
    (Set.Ioo_subset_Icc_self (rationalTime_mem_Ioo q))
  have hn := tendsto_norm_intervalCoordinate_unitDifference q ht
  have he : ∀ᶠ n in atTop,
      ‖L1Seq.intervalCoordinateOperator (unitDifference q (φ n))‖ < ε :=
    hn.eventually (gt_mem_nhds hε)
  have hj : ∀ᶠ n in atTop, N < φ n :=
    hφ.tendsto_atTop.eventually (eventually_gt_atTop N)
  obtain ⟨n, hne, hnj⟩ := (he.and hj).exists
  exact ⟨φ n, hnj, hne⟩

/-- A fixed repeating list of coordinate and sign labels. -/
noncomputable def seedSchedule : RepeatingSchedule (ℕ × Bool) :=
  RepeatingSchedule.ofCountable (ℕ × Bool)

/-- The detected coordinate is always different from the distinguished axis. -/
noncomputable def seedCoordinate (n : ℕ) : ℕ := (seedSchedule.toFun n).1 + 2

/-- The sign attached to the scheduled coordinate. -/
noncomputable def seedSign (n : ℕ) : ℝ := if (seedSchedule.toFun n).2 then 1 else -1

/-- Source positive times, indexed from zero. -/
noncomputable def seedTime (n : ℕ) : ℝ := 1 + (1 / 2 : ℝ) ^ (n + 1)

/-- Source perturbation radii, indexed from zero. -/
noncomputable def seedRadius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 7)

/-- All seed positive times are strictly positive. -/
theorem seedTime_pos (n : ℕ) : 0 < seedTime n := by
  unfold seedTime
  positivity

/-- All seed perturbation radii are strictly positive. -/
theorem seedRadius_pos (n : ℕ) : 0 < seedRadius n := by
  unfold seedRadius
  positivity

/-- The two remote indices satisfy both source smallness budgets. -/
theorem exists_seed_indices (n : ℕ) :
    ∃ r k : ℕ, max (n + 1) (seedCoordinate n) < r ∧ r < k ∧
      seedTime n * ‖L1Seq.intervalCoordinateOperator (unitDifference 1 r)‖ <
        seedRadius n / 2 ∧
      (n + 1 : ℝ) * ‖L1Seq.intervalCoordinateOperator
        (unitDifference (seedCoordinate n) k)‖ < seedRadius n / 2 := by
  have ht := seedTime_pos n
  have hρ := seedRadius_pos n
  have hε : 0 < seedRadius n / 2 / seedTime n := div_pos (half_pos hρ) ht
  obtain ⟨r, hr, hsmall⟩ := exists_remote_unitDifference_norm_lt 1
    (max (n + 1) (seedCoordinate n)) _ hε
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hδ : 0 < seedRadius n / 2 / (n + 1 : ℝ) := div_pos (half_pos hρ) hn
  obtain ⟨k, hk, hkSmall⟩ := exists_remote_unitDifference_norm_lt (seedCoordinate n) r _ hδ
  refine ⟨r, k, hr, hk, ?_, ?_⟩
  · have h := (lt_div_iff₀ ht).mp hsmall
    simpa only [mul_comm] using h
  · have h := (lt_div_iff₀ hn).mp hkSmall
    simpa only [mul_comm] using h

/-- The chosen remote index of the bounded base point. -/
noncomputable def seedBaseIndex (n : ℕ) : ℕ := (exists_seed_indices n).choose

/-- The chosen remote index of the amplified detector. -/
noncomputable def seedDetectorIndex (n : ℕ) : ℕ :=
  (exists_seed_indices n).choose_spec.choose

/-- The chosen indices retain their ordering and both quantitative budgets. -/
theorem seed_indices_spec (n : ℕ) :
    max (n + 1) (seedCoordinate n) < seedBaseIndex n ∧
      seedBaseIndex n < seedDetectorIndex n ∧
      seedTime n * ‖L1Seq.intervalCoordinateOperator
        (unitDifference 1 (seedBaseIndex n))‖ < seedRadius n / 2 ∧
      (n + 1 : ℝ) * ‖L1Seq.intervalCoordinateOperator
        (unitDifference (seedCoordinate n) (seedDetectorIndex n))‖ < seedRadius n / 2 :=
  (exists_seed_indices n).choose_spec.choose_spec

/-- The actual perturbed points of the source seed, with all choices fixed
independently of any point tested against the polar. -/
noncomputable def seedPoint (n : ℕ) : parametrizedSubspace axisDirection :=
  scaledDetector
    (axisSeedBase (seedTime n • unitDifference 1 (seedBaseIndex n)) (seedTime n))
    (unitDifferenceDetector axisDirection (seedCoordinate n) (seedDetectorIndex n))
    ((n + 1 : ℝ) * seedSign n)

/-- The distinguished coordinate axis is nonzero. -/
theorem seed_axis_ne_zero : axisDirection ≠ 0 := by
  intro h
  have he := congrArg (fun x : C0Seq ↦ x 1) h
  simp [axisDirection_apply] at he

/-- The selected base index is outside the distinguished coordinate. -/
theorem seedBaseIndex_ne_one (n : ℕ) : seedBaseIndex n ≠ 1 := by
  have h := (seed_indices_spec n).1
  have hc : 2 ≤ seedCoordinate n := by unfold seedCoordinate; omega
  omega

/-- The axis annihilates the selected detector's unit difference. -/
theorem pairing_seed_detector_zero (n : ℕ) :
    C0Seq.pairingL axisDirection
      (unitDifference (seedCoordinate n) (seedDetectorIndex n)) = 0 := by
  have hc : 2 ≤ seedCoordinate n := by unfold seedCoordinate; omega
  have hi := seed_indices_spec n
  have hq : seedCoordinate n ≠ 1 := by omega
  have hk : seedDetectorIndex n ≠ 1 := by omega
  rw [pairingL_unitDifference]
  simp [axisDirection_apply, hq, hk]

/-- The fixed schedule uses signs of absolute value one. -/
theorem abs_seedSign (n : ℕ) : |seedSign n| = 1 := by
  unfold seedSign
  split_ifs
  · norm_num
  · norm_num

/-- Every actual perturbed seed point has the prescribed dyadic positive time. -/
theorem positiveCoordinate_seedPoint (n : ℕ) :
    positiveCoordinate axisDirection seed_axis_ne_zero (seedPoint n) = seedTime n := by
  unfold seedPoint
  rw [positiveCoordinate_scaledDetector,
    positiveCoordinate_unitDifferenceDetector _ _ _ _ (pairing_seed_detector_zero n)]
  simp only [mul_zero, add_zero, positiveCoordinate_axisSeedBase]

/-- The actual seed points satisfy the source negative-coordinate radius bound. -/
theorem norm_negativeCoordinate_seedPoint_lt (n : ℕ) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n)‖ < seedRadius n := by
  have hbase := (seed_indices_spec n).2.2.1
  have hdet := (seed_indices_spec n).2.2.2
  have ht := seedTime_pos n
  have hn : (0 : ℝ) ≤ n + 1 := by positivity
  unfold seedPoint
  rw [negativeCoordinate_scaledDetector]
  have hb : ‖negativeCoordinate axisDirection seed_axis_ne_zero
      (axisSeedBase (seedTime n • unitDifference 1 (seedBaseIndex n)) (seedTime n))‖ <
      seedRadius n / 2 := by
    rw [norm_negativeCoordinate_axisSeedBase _ (seedBaseIndex_ne_one n),
      abs_of_pos ht, ← norm_intervalCoordinate_unitDifference]
    exact hbase
  have hh : ‖((n + 1 : ℝ) * seedSign n) •
      negativeCoordinate axisDirection seed_axis_ne_zero
        (unitDifferenceDetector axisDirection (seedCoordinate n) (seedDetectorIndex n))‖ <
      seedRadius n / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hn, abs_seedSign, mul_one,
      norm_negativeCoordinate_unitDifferenceDetector _ _ _ _ (pairing_seed_detector_zero n)]
    exact hdet
  exact (norm_add_le _ _).trans_lt (lt_of_lt_of_le (add_lt_add hb hh)
    (by linarith))

/-- The positive times stay between one and three halves. -/
theorem seedTime_bounds (n : ℕ) : 1 < seedTime n ∧ seedTime n ≤ 3 / 2 := by
  have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  have hb : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold seedTime
  rw [pow_succ] at hp ⊢
  constructor
  · linarith
  · linarith

/-- The perturbation radii are uniformly less than one. -/
theorem seedRadius_lt_one (n : ℕ) : seedRadius n < 1 := by
  unfold seedRadius
  have hb : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [pow_add]
  norm_num
  linarith

/-- The actual seed point energies are positive and uniformly bounded by three. -/
theorem quadraticPairing_seedPoint_bounds (n : ℕ) :
    0 < C0Seq.quadraticPairing (seedPoint n) ∧
      C0Seq.quadraticPairing (seedPoint n) < 3 := by
  rw [quadraticIdentity axisDirection seed_axis_ne_zero, positiveCoordinate_seedPoint]
  have ht := seedTime_bounds n
  have hn := norm_negativeCoordinate_seedPoint_lt n
  have hρ := seedRadius_lt_one n
  have hnonneg := norm_nonneg (negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n))
  constructor
  · nlinarith
  · nlinarith [sq_nonneg ‖negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n)‖]

/-- The geometric error scale tends to zero. -/
theorem seedRadius_tendsto_zero : Tendsto seedRadius atTop (𝓝 0) := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hlt : (1 / 2 : ℝ) < 1 := by norm_num
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hhalf hlt).comp
    (tendsto_add_atTop_nat 7)
  exact h

/-- The positive times accumulate at one. -/
theorem seedTime_tendsto_one : Tendsto seedTime atTop (𝓝 1) := by
  unfold seedTime
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hlt : (1 / 2 : ℝ) < 1 := by norm_num
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hhalf hlt).comp
    (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [add_zero, Function.comp_apply] using hc.add h

/-- The actual seed points converge to zero in their negative coordinates. -/
theorem negativeCoordinate_seedPoint_tendsto_zero :
    Tendsto (fun n ↦ negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ (norm_negativeCoordinate_seedPoint_lt n).le) seedRadius_tendsto_zero

/-- The bounded bases of the actual scheduled points have a uniform pairing bound. -/
theorem seedPoint_base_pairing_bound (w : C0Seq × L1Seq) (n : ℕ) :
    |C0Seq.symmetricForm w
      (axisSeedBase (seedTime n • unitDifference 1 (seedBaseIndex n)) (seedTime n))| ≤
        (21 / 2) * (‖w.1‖ + ‖w.2‖) := by
  apply abs_symmetricForm_axisSeedBase_le w _ (seedBaseIndex_ne_one n)
  rw [abs_of_pos (seedTime_pos n)]
  exact (seedTime_bounds n).2

/-- The sum of perturbation radii is smaller than the gap of distinct positive times. -/
theorem seedRadius_add_lt_time_gap {i j : ℕ} (hij : i < j) :
    seedRadius i + seedRadius j < seedTime i - seedTime j := by
  have hzero : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hone : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hpow : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (i + 1) :=
    pow_le_pow_of_le_one hzero hone hij
  have hpos : 0 < (1 / 2 : ℝ) ^ i := by positivity
  unfold seedRadius seedTime
  simp only [pow_add, pow_one] at hpow ⊢
  norm_num
  nlinarith

/-- Distinct scheduled points satisfy the Lorentz Lipschitz estimate. -/
theorem norm_negativeCoordinate_seedPoint_sub_le (i j : ℕ) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint i) -
      negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint j)‖ ≤
        |seedTime i - seedTime j| := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hgap := seedRadius_add_lt_time_gap hij
    have hi := norm_negativeCoordinate_seedPoint_lt i
    have hj := norm_negativeCoordinate_seedPoint_lt j
    have ht := norm_sub_le
      (negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint i))
      (negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint j))
    exact le_trans ht (le_trans (by linarith) (le_abs_self _))
  · subst j
    simp
  · have hgap := seedRadius_add_lt_time_gap hij
    have hi := norm_negativeCoordinate_seedPoint_lt i
    have hj := norm_negativeCoordinate_seedPoint_lt j
    have ht := norm_sub_le
      (negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint i))
      (negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint j))
    have habs : seedTime j - seedTime i ≤ |seedTime i - seedTime j| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact le_trans ht (le_trans (by linarith) habs)

/-- The difference of any two scheduled seed points has nonnegative pairing. -/
theorem quadraticPairing_seedPoint_sub_nonneg (i j : ℕ) :
    0 ≤ C0Seq.quadraticPairing
      ((seedPoint i : C0Seq × L1Seq) - (seedPoint j : C0Seq × L1Seq)) := by
  have he := quadraticIdentity axisDirection seed_axis_ne_zero (seedPoint i - seedPoint j)
  rw [map_sub, map_sub, positiveCoordinate_seedPoint, positiveCoordinate_seedPoint] at he
  have hb := norm_negativeCoordinate_seedPoint_sub_le i j
  have hs := (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mpr hb
  rw [sq_abs] at hs
  rw [← Submodule.coe_sub]
  rw [he]
  linarith

/-- The set of actual scheduled detector perturbations is monotone. -/
theorem seedPoint_range_isMonotone :
    C0Seq.coordinateDualPairing.IsMonotone
      (Set.range (fun n ↦ (seedPoint n : C0Seq × L1Seq))) := by
  apply (C0Seq.coordinateDualPairing.isMonotone_iff_subset_polar _).2
  rintro z ⟨i, rfl⟩
  rw [C0Seq.coordinateDualPairing.mem_monotonePolar]
  rintro w ⟨j, rfl⟩
  rw [← C0Seq.quadraticPairing_eq_coordinateQuadratic]
  exact quadraticPairing_seedPoint_sub_nonneg i j

/-- Remote detector indices escape every finite prefix. -/
theorem seedDetectorIndex_tendsto_atTop : Tendsto seedDetectorIndex atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro n
  have h := seed_indices_spec n
  change n ≤ seedDetectorIndex n
  omega

/-- The unscaled detectors have vanishing interval coordinates. -/
theorem seedDetector_interval_tendsto_zero :
    Tendsto (fun n ↦ L1Seq.intervalCoordinateOperator
      (unitDifference (seedCoordinate n) (seedDetectorIndex n))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ seedRadius_tendsto_zero
  intro n
  have h := (seed_indices_spec n).2.2.2
  have hn : (1 : ℝ) ≤ n + 1 := by
    have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnorm := norm_nonneg (L1Seq.intervalCoordinateOperator
    (unitDifference (seedCoordinate n) (seedDetectorIndex n)))
  have hρ := seedRadius_pos n
  nlinarith

/-- Along the fixed occurrence subsequence, the detector pairing converges
to the corresponding residual coordinate. -/
theorem seedDetector_pairing_tendsto (x : C0Seq) (u : L1Seq) (q : ℕ) (b : Bool) :
    Tendsto (fun k ↦ C0Seq.symmetricForm (x, u)
      (unitDifferenceDetector axisDirection
        (seedCoordinate (seedSchedule.occurrence (q, b) k))
        (seedDetectorIndex (seedSchedule.occurrence (q, b) k))))
      atTop (𝓝 ((x + L1Seq.positiveOperator u) (q + 2))) := by
  let f := seedSchedule.occurrence (q, b)
  have hf : Tendsto f atTop atTop := (seedSchedule.strictMono_occurrence (q, b)).tendsto_atTop
  have hq (k : ℕ) : seedCoordinate (f k) = q + 2 := by
    unfold seedCoordinate f
    rw [seedSchedule.apply_occurrence]
  have hx : Tendsto (fun k ↦ (x + L1Seq.positiveOperator u) (seedDetectorIndex (f k)))
      atTop (𝓝 0) :=
    (C0Seq.tendsto_zero (x + L1Seq.positiveOperator u)).comp
      (seedDetectorIndex_tendsto_atTop.comp hf)
  have hc : Tendsto (fun _ : ℕ ↦ (x + L1Seq.positiveOperator u) (q + 2)) atTop
      (𝓝 ((x + L1Seq.positiveOperator u) (q + 2))) := tendsto_const_nhds
  have hv := seedDetector_interval_tendsto_zero.comp hf
  have hu : Tendsto (fun _ : ℕ ↦ L1Seq.intervalCoordinateOperator u) atTop
      (𝓝 (L1Seq.intervalCoordinateOperator u)) := tendsto_const_nhds
  have hi : Tendsto (fun k ↦ ⟪L1Seq.intervalCoordinateOperator u,
      L1Seq.intervalCoordinateOperator
        (unitDifference (seedCoordinate (f k)) (seedDetectorIndex (f k)))⟫_ℝ)
      atTop (𝓝 0) := by
    simpa only [inner_zero_right, Function.comp_apply] using hu.inner hv
  have he (k : ℕ) : C0Seq.symmetricForm (x, u)
      (unitDifferenceDetector axisDirection (seedCoordinate (f k)) (seedDetectorIndex (f k))) =
      (x + L1Seq.positiveOperator u) (q + 2) -
        (x + L1Seq.positiveOperator u) (seedDetectorIndex (f k)) -
        2 * ⟪L1Seq.intervalCoordinateOperator u, L1Seq.intervalCoordinateOperator
          (unitDifference (seedCoordinate (f k)) (seedDetectorIndex (f k)))⟫_ℝ := by
    rw [symmetricForm_unitDifferenceDetector _ _ _ _ _ (pairing_seed_detector_zero (f k)),
      pairing_seed_detector_zero, mul_zero, sub_zero, pairingL_unitDifference, hq]
  have h := (hc.sub hx).sub (hi.const_mul 2)
  have hout := h.congr' (Eventually.of_forall (fun k ↦ (he k).symm))
  simpa only [mul_zero, sub_zero] using hout

end Lorentz
