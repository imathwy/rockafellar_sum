module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

public section

universe u v

/-- A continuous linear map between real normed spaces has dense range when the annihilator of
its range in the continuous dual is trivial. -/
theorem denseRange_of_annihilator_eq_bot {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F)
    (h_ann : StrongDual.polarSubmodule ℝ T.range = ⊥) : DenseRange T := by
  rw [denseRange_iff_closure_range]
  let K : Submodule ℝ F := T.range.topologicalClosure
  have hKtop : K = ⊤ := by
    apply Submodule.eq_top_iff'.2
    intro x
    by_contra hx
    have hconv : Convex ℝ (K : Set F) := K.convex
    have hclosed : IsClosed (K : Set F) :=
      Submodule.isClosed_topologicalClosure T.range
    obtain ⟨φ, u, hφK, hφx⟩ :=
      geometric_hahn_banach_closed_point hconv hclosed hx
    have hu : 0 < u := by
      simpa using hφK 0 K.zero_mem
    have h_le_zero : ∀ z : F, z ∈ K → φ z ≤ 0 := by
      intro z hz
      by_contra hz_not
      have hz_pos : 0 < φ z := lt_of_not_ge hz_not
      let c : ℝ := u / φ z + 1
      have hc_pos : 0 < c := by
        dsimp [c]
        positivity
      have hcz := hφK (c • z) (K.smul_mem c hz)
      have hcz' : c * φ z < u := by
        simpa [map_smul, smul_eq_mul, c] using hcz
      have hdiv : (u / φ z) * φ z = u := by
        exact div_mul_cancel₀ u (ne_of_gt hz_pos)
      nlinarith
    have hφK_zero : ∀ z : F, z ∈ K → φ z = 0 := by
      intro z hz
      have h₁ := h_le_zero z hz
      have h₂ := h_le_zero (-z) (K.neg_mem hz)
      have h₂' : 0 ≤ φ z := by
        simpa using h₂
      exact le_antisymm h₁ h₂'
    have hφ_ann : φ ∈ StrongDual.polarSubmodule ℝ T.range :=
      (StrongDual.mem_polarSubmodule ℝ T.range φ).2 (by
        intro z hz
        exact hφK_zero z (by
          exact Submodule.le_topologicalClosure T.range hz))
    have hφ_zero : φ = 0 := by
      have hφ_bot : φ ∈ (⊥ : Submodule ℝ (StrongDual ℝ F)) := by
        rw [← h_ann]
        exact hφ_ann
      exact (Submodule.mem_bot ℝ).1 hφ_bot
    have hφx' : u < 0 := by
      simpa [hφ_zero] using hφx
    linarith
  change (K : Set F) = Set.univ
  rw [hKtop]
  rfl
