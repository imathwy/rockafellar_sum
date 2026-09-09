/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedBase
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.ScaledDetector
public import ReasLib.Data.Countable.RepeatingSchedule

/-!
# Fixed signed schedule for the S3 seed

Natural index n represents source index n + 1. The signed coordinate label
(q, b) represents coordinate q + 2 and sign determined by b.
-/

public section

open Filter Topology

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

end Lorentz
