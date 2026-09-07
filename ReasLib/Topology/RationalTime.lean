module

public import ReasLib.Topology.Sequences
public import ReasLib.Order.RationalTime

open Topology

/-- The canonical rational-time enumeration, regarded as taking values in the closed unit
interval. -/
private noncomputable def unitIntervalRationalTime (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  -- Restrict the codomain using the strict bounds already known for every enumerated time.
  ⟨rationalTime n, Set.Ioo_subset_Icc_self (rationalTime_mem_Ioo n)⟩

/-- Coercing a unit-interval rational time to `ℝ` recovers the original enumeration. -/
private lemma coe_unitIntervalRationalTime (n : ℕ) :
    (unitIntervalRationalTime n : ℝ) = rationalTime n := by
  -- Expose only the value projection of the subtype-valued enumeration.
  rfl

/-- Every neighborhood in the closed unit interval contains an enumerated rational time
beyond any prescribed index. -/
private lemma exists_gt_unitIntervalRationalTime_mem_of_mem_nhds
    (b : Set.Icc (0 : ℝ) 1) (U : Set (Set.Icc (0 : ℝ) 1)) (hU : U ∈ nhds b) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ unitIntervalRationalTime n ∈ U := by
  -- It suffices to place a tail term in a sufficiently small metric ball around `b`.
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hU
  by_cases hb : b.1 < 1
  · let η : ℝ := min (ε / 2) ((1 - b.1) / 2)
    have hηpos : 0 < η := by
      apply lt_min
      · linarith
      · linarith
    have hηeps : η < ε := by
      have hηle := min_le_left (ε / 2) ((1 - b.1) / 2)
      linarith
    have hηunit : b.1 + η < 1 := by
      have hηle := min_le_right (ε / 2) ((1 - b.1) / 2)
      linarith
    have hInterval : Set.Ioo b.1 (b.1 + η) ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨b.property.1.trans_lt hy.1, hy.2.trans hηunit⟩
    -- Tail density in the short right-hand interval supplies the desired index.
    obtain ⟨n, hnN, hnInterval⟩ :=
      exists_gt_rationalTime_mem_Ioo (lt_add_of_pos_right b.1 hηpos) hInterval N
    refine ⟨n, hnN, hBall ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, coe_unitIntervalRationalTime]
    rw [abs_of_pos (sub_pos.mpr hnInterval.1)]
    linarith [hnInterval.2]
  · have hbOne : b.1 = 1 := le_antisymm b.property.2 (le_of_not_gt hb)
    let η : ℝ := min (ε / 2) (1 / 2)
    have hηpos : 0 < η := by
      apply lt_min
      · linarith
      · norm_num
    have hηeps : η < ε := by
      have hηle := min_le_left (ε / 2) (1 / 2)
      linarith
    have hηzero : 0 < b.1 - η := by
      have hηle := min_le_right (ε / 2) (1 / 2)
      linarith
    have hInterval : Set.Ioo (b.1 - η) b.1 ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨hηzero.trans hy.1, hy.2.trans_le b.property.2⟩
    -- At the right endpoint, approach through a short interval lying to its left.
    obtain ⟨n, hnN, hnInterval⟩ :=
      exists_gt_rationalTime_mem_Ioo (sub_lt_self b.1 hηpos) hInterval N
    refine ⟨n, hnN, hBall ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, coe_unitIntervalRationalTime]
    rw [abs_of_neg (sub_neg.mpr hnInterval.2)]
    linarith [hnInterval.1]

/-- Every point of the unit interval is the limit of a strictly increasing
subsequence of the canonical enumeration of rational times. -/
public theorem exists_strictMono_rationalTime_tendsto (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (rationalTime ∘ φ) Filter.atTop (𝓝 t) := by
  let b : Set.Icc (0 : ℝ) 1 := ⟨t, ht⟩
  -- Apply the generic tail-visitation theorem in the correct ambient subtype.
  obtain ⟨φ, hφ, hφTendsto⟩ :=
    exists_strictMono_subseq_tendsto unitIntervalRationalTime
      exists_gt_unitIntervalRationalTime_mem_of_mem_nhds b
  refine ⟨φ, hφ, ?_⟩
  -- Continuous subtype coercion transports the resulting convergence back to `ℝ`.
  have hProjected := (continuous_subtype_val.tendsto b).comp hφTendsto
  have hCoeComp :
      Subtype.val ∘ unitIntervalRationalTime ∘ φ = rationalTime ∘ φ := by
    -- Identify the projected subtype sequence pointwise with the original enumeration.
    funext n
    exact coe_unitIntervalRationalTime (φ n)
  rw [← hCoeComp]
  exact hProjected

/-- A real-valued function continuous on the unit interval and converging to
zero along the canonical rational-time sequence vanishes on the interval. -/
public theorem continuousOn_eq_zero_of_tendsto_rationalTime (G : ℝ → ℝ)
    (h_cont : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (h_samples : Filter.Tendsto (fun n : ℕ ↦ G (rationalTime n))
      Filter.atTop (𝓝 0)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, G t = 0 := by
  intro t ht
  -- Select a tail subsequence of rational times converging to the prescribed point.
  obtain ⟨φ, hφmono, hφlim⟩ := exists_strictMono_rationalTime_tendsto t ht
  have hφmem :
      ∀ᶠ k in Filter.atTop, (rationalTime ∘ φ) k ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun k ↦
      Set.Ioo_subset_Icc_self (rationalTime_mem_Ioo (φ k))
  have hSubsequenceWithin :
      Filter.Tendsto (rationalTime ∘ φ) Filter.atTop
        (𝓝[Set.Icc (0 : ℝ) 1] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (rationalTime ∘ φ) hφlim hφmem
  -- Continuity and convergence of the full sample sequence give the two subsequential limits.
  have hContinuousSubsequence :
      Filter.Tendsto (fun k ↦ G (rationalTime (φ k))) Filter.atTop (𝓝 (G t)) := by
    simpa only [Function.comp_def] using
      Filter.Tendsto.comp (h_cont t ht) hSubsequenceWithin
  have hZeroSubsequence :
      Filter.Tendsto (fun k ↦ G (rationalTime (φ k))) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      Filter.Tendsto.comp h_samples hφmono.tendsto_atTop
  -- Hausdorff uniqueness identifies the two limits of the common subsequence.
  exact tendsto_nhds_unique hContinuousSubsequence hZeroSubsequence
