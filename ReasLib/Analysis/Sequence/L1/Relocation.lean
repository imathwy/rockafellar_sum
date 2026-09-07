module

public import ReasLib.Analysis.Sequence.L1

@[expose] public section

noncomputable section

namespace L1Seq

/-- Relocate the finitely many nonzero coordinates of `b` along the index map `m`. -/
noncomputable def remoteCopy (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport)
    (m : ℕ → ℕ) : L1Seq :=
  ∑ i ∈ h_b.toFinset, lp.single 1 (m i) (b i)

/-- A coordinate of `remoteCopy b h_b m` is the sum of the source coefficients sent there. -/
theorem remoteCopy_apply (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport)
    (m : ℕ → ℕ) (j : ℕ) :
    remoteCopy b h_b m j = ∑ i ∈ h_b.toFinset, if m i = j then b i else 0 := by
  -- Evaluate each coordinate singleton and orient its index test as in the target sum.
  classical
  simp only [remoteCopy, lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
    Pi.single_apply, eq_comm]

/-- An injective relocation on the support places each nonzero coefficient at its image. -/
theorem remoteCopy_apply_of_mem_support
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ)
    (h_m : Set.InjOn m (Function.support fun i ↦ b i)) (i : ℕ) (h_i : b i ≠ 0) :
    remoteCopy b h_b m (m i) = b i := by
  -- Injectivity on the support makes `i` the unique nonzero summand over `m i`.
  classical
  have hiSupport : i ∈ Function.support (fun k ↦ b k) := h_i
  have hiFinset : i ∈ h_b.toFinset := h_b.mem_toFinset.mpr hiSupport
  rw [remoteCopy_apply, Finset.sum_eq_single i]
  · simp only [if_true]
  · intro k hk hki
    have hkSupport : k ∈ Function.support (fun n ↦ b n) := h_b.mem_toFinset.mp hk
    have hmk : m k ≠ m i := fun hEq ↦ hki (h_m hkSupport hiSupport hEq)
    simp only [hmk, if_false]
  · exact fun hi ↦ (hi hiFinset).elim

/-- An injective relocation carries the support exactly to its image under `m`. -/
theorem support_remoteCopy
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ)
    (h_m : Set.InjOn m (Function.support fun i ↦ b i)) :
    Function.support (fun j ↦ remoteCopy b h_b m j) =
      m '' Function.support (fun i ↦ b i) := by
  -- A copied coordinate is nonzero exactly when it is the image of a source-support index.
  classical
  ext j
  simp only [Function.mem_support, Set.mem_image]
  constructor
  · intro hj
    by_contra hjImage
    apply hj
    rw [remoteCopy_apply]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [if_neg]
    intro hmi
    exact hjImage ⟨i, h_b.mem_toFinset.mp hi, hmi⟩
  · rintro ⟨i, hi, rfl⟩
    rw [remoteCopy_apply_of_mem_support b h_b m h_m i hi]
    exact hi

/-- Relocating every nonzero coefficient past `N` puts the copied support in `Set.Ioi N`. -/
theorem support_remoteCopy_subset_Ioi
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ)
    (h_m : Set.InjOn m (Function.support fun i ↦ b i)) (N : ℕ)
    (h_tail : ∀ i, b i ≠ 0 → N < m i) :
    Function.support (fun j ↦ remoteCopy b h_b m j) ⊆ Set.Ioi N := by
  -- Rewrite the copied support as an image and apply the tail bound to its preimage.
  intro j hj
  rw [support_remoteCopy b h_b m h_m] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact h_tail i hi

/-- Relocating along a map injective on the support preserves the `L1Seq` norm. -/
theorem norm_remoteCopy
    (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ)
    (h_m : Set.InjOn m (Function.support fun i ↦ b i)) :
    ‖remoteCopy b h_b m‖ = ‖b‖ := by
  -- Restrict both norm sums to their finite supports, then reindex along `m`.
  classical
  have hmFinset : Set.InjOn m (↑h_b.toFinset : Set ℕ) := by
    intro i hi k hk hik
    exact h_m (h_b.mem_toFinset.mp hi) (h_b.mem_toFinset.mp hk) hik
  have hSourceSum : ∑' i, |b i| = ∑ i ∈ h_b.toFinset, |b i| := by
    apply tsum_eq_sum
    intro i hi
    have hbi : b i = 0 := by
      by_contra hne
      exact hi (h_b.mem_toFinset.mpr hne)
    simp only [hbi, abs_zero]
  have hCopySum :
      ∑' j, |remoteCopy b h_b m j| =
        ∑ j ∈ h_b.toFinset.image m, |remoteCopy b h_b m j| := by
    apply tsum_eq_sum
    intro j hj
    simp only [abs_eq_zero]
    by_contra hne
    have hjSupport : j ∈ Function.support (fun k ↦ remoteCopy b h_b m k) := hne
    rw [support_remoteCopy b h_b m h_m] at hjSupport
    obtain ⟨i, hi, rfl⟩ := hjSupport
    exact hj (Finset.mem_image.mpr ⟨i, h_b.mem_toFinset.mpr hi, rfl⟩)
  calc
    ‖remoteCopy b h_b m‖ = ∑' j, |remoteCopy b h_b m j| := norm_eq_tsum_abs _
    _ = ∑ j ∈ h_b.toFinset.image m, |remoteCopy b h_b m j| := hCopySum
    _ = ∑ i ∈ h_b.toFinset, |remoteCopy b h_b m (m i)| :=
      Finset.sum_image hmFinset
    _ = ∑ i ∈ h_b.toFinset, |b i| := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [remoteCopy_apply_of_mem_support b h_b m h_m i (h_b.mem_toFinset.mp hi)]
    _ = ∑' i, |b i| := hSourceSum.symm
    _ = ‖b‖ := (norm_eq_tsum_abs b).symm

end L1Seq
