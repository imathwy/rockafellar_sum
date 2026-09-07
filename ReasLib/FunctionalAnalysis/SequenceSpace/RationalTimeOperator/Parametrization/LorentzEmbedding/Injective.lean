module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.Kernel

public section

namespace Lorentz

/-- The Lorentz embedding on a parametrized subspace is injective. -/
theorem embedding_injective (d : C0Seq) (hd : d ≠ 0) :
    Function.Injective (embedding d hd) := by
  intro z w h
  -- Route correction: project to the negative coordinate and use its explicit `map_sub` law.
  -- Equality of embeddings first gives equality of their negative coordinates.
  have hNegative := congrArg Prod.snd h
  rw [embedding_apply, embedding_apply] at hNegative
  -- Linearity turns that coordinate equality into vanishing on the difference.
  have hN : negativeCoordinate d hd (z - w) = 0 := by
    calc
      negativeCoordinate d hd (z - w) =
          negativeCoordinate d hd z - negativeCoordinate d hd w :=
        (negativeCoordinate d hd).map_sub z w
      _ = 0 := sub_eq_zero.mpr hNegative
  -- The negative-coordinate kernel is trivial, so the original points agree.
  have hzero : z - w = 0 :=
    eq_zero_of_negativeCoordinate_eq_zero d hd (z - w) hN
  exact sub_eq_zero.mp hzero

end Lorentz
