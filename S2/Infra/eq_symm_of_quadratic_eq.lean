module

public import ReasLib.Analysis.Normed.Operator.Bilinear

universe u

/- Infrastructure C.2 (Polarization of a real quadratic operator identity): continuous
real bilinear forms with equal diagonal values have equal symmetric parts. -/
#check (ContinuousLinearMap.add_flip_eq_add_flip_of_diagonal_eq :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B C : E →L[ℝ] E →L[ℝ] ℝ), (∀ x, B x x = C x x) → B + B.flip = C + C.flip)
