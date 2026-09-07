module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.QuadraticIdentity
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Injective

namespace L1Seq

/-- The quadratic pairing of `positiveOperator a` with a nonzero `a` is strictly
positive. -/
public theorem positiveOperator_quadratic_pos (a : L1Seq) (ha : a ≠ 0) :
    0 < C0Seq.pairingL (positiveOperator a) a := by
  -- Rewrite the quadratic pairing as the squared interval-coordinate norm.
  rw [positiveOperator_quadratic_eq_norm_sq]
  -- Injectivity of the interval-coordinate operator makes that norm nonzero.
  have hV : intervalCoordinateOperator a ≠ 0 := by
    intro hV
    apply ha
    have hV0 : intervalCoordinateOperator a = intervalCoordinateOperator 0 := by
      simpa using hV
    exact intervalCoordinateOperator_injective hV0
  -- A positive norm has a strictly positive square.
  exact sq_pos_of_pos (norm_pos_iff.mpr hV)

/-- The rational-time positive operator on real summable sequences is injective. -/
public theorem positiveOperator_injective :
    Function.Injective positiveOperator := by
  intro a b hab
  by_contra hne
  -- A nonzero difference has strictly positive quadratic pairing.
  have hdiff : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < C0Seq.pairingL (positiveOperator (a - b)) (a - b) :=
    positiveOperator_quadratic_pos (a - b) hdiff
  -- Linearity and equality of the two images make the same pairing vanish.
  have hzero : C0Seq.pairingL (positiveOperator (a - b)) (a - b) = 0 := by
    have hA : positiveOperator (a - b) = 0 := by
      rw [map_sub, hab]
      simp
    rw [hA]
    simp
  exact (ne_of_gt hpos) hzero

end L1Seq
