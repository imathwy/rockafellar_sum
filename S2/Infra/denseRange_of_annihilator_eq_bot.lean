module

public import ReasLib.Analysis.Normed.Module.Dual

public section

universe u v

/- Infrastructure C.7 (Dense range from a trivial continuous annihilator) -/
#check (denseRange_of_annihilator_eq_bot :
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F),
    StrongDual.polarSubmodule ℝ T.range = ⊥ → DenseRange T)
