module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization

public section

namespace Lorentz

/-- A nonzero direction makes the rational-time parametrization injective. -/
theorem parametrization_injective (d : C0Seq) (hd : d ≠ 0) :
    Function.Injective (parametrization d) := by
  intro x y hxy
  rcases x with ⟨a, t⟩
  rcases y with ⟨b, s⟩
  -- The second coordinate records the `L1Seq` parameter unchanged.
  have hab : a = b := by
    simpa only [parametrization_apply] using congrArg Prod.snd hxy
  subst b
  -- Equality of first coordinates then reduces to equality of the scalar multiples.
  have hsmul : t • d = s • d := by
    apply add_left_cancel (a := -L1Seq.positiveOperator a)
    simpa only [parametrization_apply] using congrArg Prod.fst hxy
  -- A nonzero direction makes scalar multiplication faithful in its scalar argument.
  have hts : t = s := (smul_left_injective ℝ hd) hsmul
  subst s
  rfl

end Lorentz
