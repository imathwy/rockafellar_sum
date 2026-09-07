module

public import ReasLib.Analysis.Normed.LorentzCone
public import ReasLib.Analysis.InnerProductSpace.HilbertProd2

@[expose] public section

universe u

namespace Lorentz

/-- A norm-square and a scalar product are a difference of shifted squares. -/
theorem completeSquare {H : Type u} [Norm H] (v : H) (s t : ℝ) :
    -(‖v‖ ^ 2) + t * s =
      ((t + s) / 2) ^ 2 - (‖v‖ ^ 2 + ((t - s) / 2) ^ 2) := by
  -- Expanding both shifted squares reduces the claim to a polynomial identity over `ℝ`.
  ring

/-- The completed-square expression is the Lorentz energy of the corresponding
`HilbertProd2` coordinates. -/
theorem completeSquareEnergy {H : Type u} [NormedAddCommGroup H]
    (v : H) (s t : ℝ) :
    -(‖v‖ ^ 2) + t * s =
      energy ((t + s) / 2, HilbertProd2.mk v ((t - s) / 2)) := by
  -- Compute the energy and product norm, then reuse the scalar completed-square identity.
  rw [energy_apply, HilbertProd2.norm_mk_sq]
  exact completeSquare v s t

end Lorentz
