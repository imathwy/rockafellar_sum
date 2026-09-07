module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

public section

universe u v w

namespace ContinuousLinearMap

/-- Two continuous linear maps into a strong dual are equal when their values agree on
every vector of the primal space. -/
@[ext]
theorem strongDual_ext
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (S T : X →L[𝕜] StrongDual 𝕜 Y)
    (h : ∀ x : X, ∀ y : Y, S x y = T x y) :
    S = T := by
  -- First identify the two maps by fixing an arbitrary vector in their domain.
  apply ContinuousLinearMap.ext
  intro x
  -- Their strong-dual values are functionals, so pointwise agreement on `Y` finishes.
  apply ContinuousLinearMap.ext
  intro y
  exact h x y

end ContinuousLinearMap
