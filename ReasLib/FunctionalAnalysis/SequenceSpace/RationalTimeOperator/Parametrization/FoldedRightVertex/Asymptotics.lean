module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector.FavorableSign
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorIndex.Pairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Pairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Bounds

public section

open Filter Topology

namespace Lorentz

/-- The negative coordinates of the folded right vertices converge to zero. -/
theorem rightVertex_tendsto_ghost (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ negativeCoordinate d hd
      (rightVertex d hd h_missing h h_tendsto i)) atTop (𝓝 0) := by
  -- The scheduled right radii decay to zero because they are a fixed dyadic power tail.
  have hR : Tendsto (fun i ↦ DetectorTriple.rightRadius i) atTop (𝓝 0) := by
    have hexp : Tendsto (fun i : ℕ => -((i : ℝ) + 6)) atTop atBot := by
      exact Filter.tendsto_neg_atTop_atBot.comp
        (Filter.tendsto_atTop_add_const_right _ 6 tendsto_natCast_atTop_atTop)
    have hpow : Tendsto (fun x : ℝ => (2 : ℝ) ^ x) atBot (𝓝 0) :=
      tendsto_rpow_atBot_of_base_gt_one (2 : ℝ) (by norm_num)
    have hpow' : Tendsto (fun i : ℕ => (2 : ℝ) ^ (-((i : ℝ) + 6)))
        atTop (𝓝 0) := by
      change Tendsto ((fun x : ℝ => (2 : ℝ) ^ x) ∘
        (fun i : ℕ => -((i : ℝ) + 6))) atTop (𝓝 0)
      exact hpow.comp hexp
    simpa only [DetectorTriple.rightRadius_def] using hpow'
  -- Reuse the coordinate API bound and squeeze by the vanishing radius envelope.
  refine squeeze_zero_norm
    (f := fun i => negativeCoordinate d hd
      (rightVertex d hd h_missing h h_tendsto i))
    (a := fun i => DetectorTriple.rightRadius i) (fun i => ?_) hR
  exact (norm_negativeCoordinate_rightVertex_lt d hd h_missing h h_tendsto i).le

/-- The pairing gap of the folded right vertices exceeds every real threshold
at arbitrarily late indices. -/
theorem rightVertex_sub_quadraticPairing_cofinal
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (w : C0Seq × L1Seq) (hw : w ∉ parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (h_pairing : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w))) :
    ∀ (R : ℝ) (N : ℕ), ∃ i : ℕ, N ≤ i ∧
      R < C0Seq.symmetricForm w (rightVertex d hd h_missing h h_tendsto i) -
        C0Seq.quadraticPairing (rightVertex d hd h_missing h h_tendsto i) := by
  intro R N
  obtain ⟨t, ht⟩ := exists_detectorTriple_pos d w hd hw
  obtain ⟨η, hη, hη_event⟩ := eventually_pos_signedDetectorReading
    d hd h_missing w hw h h_tendsto h_pairing t ht
  have hocc : Tendsto (DetectorTriple.schedule.occurrence t) atTop atTop :=
    (DetectorTriple.schedule.strictMono_occurrence t).tendsto_atTop
  have hscale_occ : Tendsto
      (fun k ↦ detectorScale d hd h_missing
        (DetectorTriple.schedule.occurrence t k)) atTop atTop :=
    (tendsto_detectorScale d hd h_missing).comp hocc
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 2 * C0Seq.zSize w / η < J :=
    exists_nat_gt (2 * C0Seq.zSize w / η)
  have hC : 0 ≤ C0Seq.zSize w := by
    rw [C0Seq.zSize_apply]
    positivity
  obtain ⟨k, hkN, hkJ, hkScale, hkRead⟩ : ∃ k : ℕ,
      N ≤ DetectorTriple.schedule.occurrence t k ∧
        J ≤ DetectorTriple.schedule.occurrence t k ∧
        2 * (R + 3) / η < detectorScale d hd h_missing
          (DetectorTriple.schedule.occurrence t k) ∧
        η ≤ (t.sign : ℝ) * C0Seq.symmetricForm w
          (h t.p t.q t.p_lt_q
            (detectorIndex d hd h_missing h h_tendsto
              (DetectorTriple.schedule.occurrence t k))) := by
    have hN_evt := hocc.eventually (eventually_ge_atTop N)
    have hJ_evt := hocc.eventually (eventually_ge_atTop J)
    have hS_evt := hscale_occ.eventually
      (eventually_gt_atTop (2 * (R + 3) / η))
    have hall : ∀ᶠ k in atTop,
        N ≤ DetectorTriple.schedule.occurrence t k ∧
          J ≤ DetectorTriple.schedule.occurrence t k ∧
          2 * (R + 3) / η < detectorScale d hd h_missing
            (DetectorTriple.schedule.occurrence t k) ∧
          η ≤ (t.sign : ℝ) * C0Seq.symmetricForm w
            (h t.p t.q t.p_lt_q
              (detectorIndex d hd h_missing h h_tendsto
                (DetectorTriple.schedule.occurrence t k))) := by
      exact hN_evt.and (hJ_evt.and (hS_evt.and hη_event))
    obtain ⟨k, hk⟩ := hall.exists
    rcases hk with ⟨hkN, hkJ, hkScale, hkRead⟩
    exact ⟨k, hkN, hkJ, hkScale, hkRead⟩
  let i := DetectorTriple.schedule.occurrence t k
  have hiN : N ≤ i := hkN
  have hiJ : J ≤ i := hkJ
  have hcoeff : C0Seq.zSize w / (((i + 1 : ℕ) : ℝ) ^ 2) < η / 2 := by
    have hJmul : 2 * C0Seq.zSize w < (J : ℝ) * η :=
      (div_lt_iff₀ hη).mp hJ
    have hdenJ : (J : ℝ) ≤ (((i + 1 : ℕ) : ℝ) ^ 2) := by
      have hJi : (J : ℝ) ≤ (i : ℝ) := by exact_mod_cast hiJ
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith [hJi, sq_nonneg (i : ℝ)]
    have hmul : (η / 2) * (J : ℝ) ≤
        (η / 2) * (((i + 1 : ℕ) : ℝ) ^ 2) := by
      gcongr
    have hCden : C0Seq.zSize w <
        (η / 2) * (((i + 1 : ℕ) : ℝ) ^ 2) := by
      exact lt_of_lt_of_le (by nlinarith [hJmul]) hmul
    apply (div_lt_iff₀ (by positivity :
      0 < (((i + 1 : ℕ) : ℝ) ^ 2))).2
    exact hCden
  have hscale_pos : 0 < detectorScale d hd h_missing i :=
    detectorScale_pos d hd h_missing i
  have hscale_lower : 2 * (R + 3) / η < detectorScale d hd h_missing i := by
    exact hkScale
  have hscheduled :
      scheduledDetectorPoint h i
          (detectorIndex d hd h_missing h h_tendsto i) =
        h t.p t.q t.p_lt_q
          (detectorIndex d hd h_missing h h_tendsto i) := by
    unfold i
    rw [scheduledDetectorPoint_apply,
      DetectorTriple.schedule.apply_occurrence]
  have hread : η ≤ (t.sign : ℝ) * C0Seq.symmetricForm w
      (scheduledDetectorPoint h i
        (detectorIndex d hd h_missing h h_tendsto i)) := by
    simpa [hscheduled] using hkRead
  have hread_pos : 0 < (t.sign : ℝ) * C0Seq.symmetricForm w
      (scheduledDetectorPoint h i
        (detectorIndex d hd h_missing h h_tendsto i)) :=
    lt_of_lt_of_le hη hread
  have hscaled_read :
      detectorScale d hd h_missing i * η ≤
        detectorScale d hd h_missing i *
          ((t.sign : ℝ) * C0Seq.symmetricForm w
            (scheduledDetectorPoint h i
              (detectorIndex d hd h_missing h h_tendsto i))) :=
    mul_le_mul_of_nonneg_left hread hscale_pos.le
  have hlarge : 2 * (R + 3) < detectorScale d hd h_missing i * η :=
    (div_lt_iff₀ hη).mp hscale_lower
  refine ⟨i, hiN, ?_⟩
  have hexpand := symmetricForm_rightVertex_sub_quadraticPairing
    d hd h_missing h h_tendsto w i
  dsimp at hexpand
  have hξ_abs := abs_symmetricForm_nearGhostBase_le_zSize
    d hd h_missing w i
  have hξ_nonneg : 0 ≤ C0Seq.zSize (nearGhostBase d hd h_missing i) := by
    rw [C0Seq.zSize_apply]
    positivity
  have hscale_formula := detectorScale_apply d hd h_missing i
  have hA_pos : 0 < (((i + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hξ_scale :
      C0Seq.zSize w * C0Seq.zSize (nearGhostBase d hd h_missing i) ≤
        detectorScale d hd h_missing i *
          (C0Seq.zSize w / (((i + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [hscale_formula]
    have hfactor :
        (((i + 1 : ℕ) : ℝ) ^ 2) *
            (1 + C0Seq.zSize (nearGhostBase d hd h_missing i)) *
            (C0Seq.zSize w / (((i + 1 : ℕ) : ℝ) ^ 2)) =
          C0Seq.zSize w *
            (1 + C0Seq.zSize (nearGhostBase d hd h_missing i)) := by
      field_simp [ne_of_gt hA_pos]
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left (by linarith [hξ_nonneg]) hC
  have hξ_small :
      C0Seq.zSize w * C0Seq.zSize (nearGhostBase d hd h_missing i) <
        detectorScale d hd h_missing i * (η / 2) := by
    exact lt_of_le_of_lt hξ_scale
      (mul_lt_mul_of_pos_left hcoeff hscale_pos)
  have hBξ_lower :
      -(detectorScale d hd h_missing i * (η / 2)) ≤
        C0Seq.symmetricForm w (nearGhostBase d hd h_missing i) := by
    calc
      -(detectorScale d hd h_missing i * (η / 2)) ≤
          -(C0Seq.zSize w * C0Seq.zSize (nearGhostBase d hd h_missing i)) :=
        neg_le_neg hξ_small.le
      _ ≤ C0Seq.symmetricForm w (nearGhostBase d hd h_missing i) :=
        neg_le_of_abs_le hξ_abs
  have hcξ_lower :
      -(9 : ℝ) / 4 ≤
        -C0Seq.quadraticPairing (nearGhostBase d hd h_missing i) := by
    have habs := abs_quadraticPairing_nearGhostBase_le d hd h_missing i
    have hq_upper : C0Seq.quadraticPairing (nearGhostBase d hd h_missing i) ≤
        (9 : ℝ) / 4 := le_trans (le_abs_self _) habs
    linarith
  have hBξδ_lower :
      -DetectorTriple.rightRadius i ^ 2 / 2 ≤
        -C0Seq.symmetricForm (nearGhostBase d hd h_missing i)
          (detectorPerturbation d hd h_missing h h_tendsto i) := by
    have habs := abs_symmetricForm_nearGhostBase_detectorPerturbation_lt
      d hd h_missing h h_positive h_tendsto i
    have hB_upper : C0Seq.symmetricForm (nearGhostBase d hd h_missing i)
          (detectorPerturbation d hd h_missing h h_tendsto i) ≤
        DetectorTriple.rightRadius i ^ 2 / 2 :=
      le_trans (le_abs_self _) (le_of_lt habs)
    linarith
  have hcδ_lower :
      0 ≤ -C0Seq.quadraticPairing
        (detectorPerturbation d hd h_missing h h_tendsto i) := by
    have hq := quadraticPairing_detectorPerturbation_nonpos
      d hd h_missing h h_positive h_tendsto i
    linarith
  have hradius_bound : DetectorTriple.rightRadius i ^ 2 / 2 ≤ (3 : ℝ) / 4 := by
    have hr : DetectorTriple.rightRadius i ≤ (1 : ℝ) := by
      rw [DetectorTriple.rightRadius_def]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have hi0 : (0 : ℝ) ≤ i := by positivity
      linarith
    have hr0 : 0 ≤ DetectorTriple.rightRadius i := by
      rw [DetectorTriple.rightRadius_def]
      positivity
    nlinarith
  have hrem :
      -(detectorScale d hd h_missing i * (η / 2)) - 3 ≤
        C0Seq.symmetricForm w (nearGhostBase d hd h_missing i) -
          C0Seq.quadraticPairing (nearGhostBase d hd h_missing i) -
          C0Seq.symmetricForm (nearGhostBase d hd h_missing i)
            (detectorPerturbation d hd h_missing h h_tendsto i) -
          C0Seq.quadraticPairing
            (detectorPerturbation d hd h_missing h h_tendsto i) := by
    nlinarith [hBξ_lower, hcξ_lower, hBξδ_lower, hcδ_lower,
      hradius_bound]
  have hsign : (DetectorTriple.schedule.toFun i).sign = t.sign := by
    unfold i
    rw [DetectorTriple.schedule.apply_occurrence]
  rw [hexpand]
  rw [hsign]
  have hmargin : R + 3 + detectorScale d hd h_missing i * (η / 2) <
      (((t.sign : ℝ) * detectorScale d hd h_missing i) *
        C0Seq.symmetricForm w
          (scheduledDetectorPoint h i
            (detectorIndex d hd h_missing h h_tendsto i))) := by
    nlinarith
  nlinarith [hmargin, hrem]

end Lorentz
