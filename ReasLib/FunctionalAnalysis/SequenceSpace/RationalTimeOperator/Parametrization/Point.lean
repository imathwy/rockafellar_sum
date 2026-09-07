module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization

public section

noncomputable section

namespace Lorentz

/-- The source point `Ψ(a, t)`, regarded as an element of `parametrizedSubspace d`. -/
def parametrizedPoint (d : C0Seq) (a : L1Seq) (t : ℝ) : parametrizedSubspace d :=
  ⟨parametrization d (a, t),
    mem_parametrizedSubspace d _ |>.mpr ⟨a, t, parametrization_apply d a t⟩⟩

/-- The ambient value of the parametrized point is `Ψ(a, t)`. -/
@[simp]
theorem parametrizedPoint_apply (d : C0Seq) (a : L1Seq) (t : ℝ) :
    (parametrizedPoint d a t : C0Seq × L1Seq) = parametrization d (a, t) := by
  -- Coercion from the subtype reduces to its stored ambient value.
  rfl

end Lorentz
