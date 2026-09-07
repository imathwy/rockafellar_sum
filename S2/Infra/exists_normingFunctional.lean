module

public import Mathlib.Analysis.Normed.Module.HahnBanach

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (x : E) (hx : x ≠ 0)

/- Infrastructure D.9 (A norming functional for a nonzero Banach vector): every nonzero vector
in a real normed space admits a norm-one continuous linear functional attaining its norm. -/
#check (exists_dual_vector ℝ x (norm_ne_zero_iff.mpr hx) :
  ∃ xstar : StrongDual ℝ E, ‖xstar‖ = 1 ∧ xstar x = ‖x‖)
