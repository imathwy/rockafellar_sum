module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0

public section

namespace C0Seq

/-- If every ordered two-coordinate determinant of a nonzero sequence `d` with a
sequence `r` vanishes, then `r` is a real scalar multiple of `d`. -/
theorem eq_smul_of_all_twoDet_eq_zero (d r : C0Seq) (hd : d ≠ 0)
    (h_det : ∀ p q : ℕ, p < q → d p * r q - d q * r p = 0) :
    ∃ s : ℝ, r = s • d := by
  obtain ⟨i, hi⟩ :=
    Function.support_nonempty_iff.mpr (DFunLike.coe_injective.ne hd)
  have hdi : d i ≠ 0 := Function.mem_support.mp hi
  refine ⟨r i / d i, ?_⟩
  ext n
  rw [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  by_cases hni : n = i
  · subst n
    exact (div_mul_cancel₀ (r i) hdi).symm
  · rcases Nat.lt_or_gt_of_ne hni with hlt | hgt
    · have hcross : d i * r n = d n * r i := by
        have h := h_det n i hlt
        linarith
      calc
        r n = (r i * d n) / d i := by
          apply (eq_div_iff hdi).2
          simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
        _ = (r i / d i) * d n := by ring
    · have hcross : d i * r n = d n * r i := by
        have h := h_det i n hgt
        linarith
      calc
        r n = (r i * d n) / d i := by
          apply (eq_div_iff hdi).2
          simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
        _ = (r i / d i) * d n := by ring

end C0Seq
