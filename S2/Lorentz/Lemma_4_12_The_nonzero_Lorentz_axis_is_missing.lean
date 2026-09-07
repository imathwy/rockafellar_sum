module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.Axis

public section

namespace Lorentz

/-- The ghost point on the nonzero Lorentz axis. -/
noncomputable def ghostPoint : ℝ × HilbertProd2 UnitL2 := ((1 : ℝ), 0)

variable (d : C0Seq) (hd : d ≠ 0)

/- Lemma 4.12 (The nonzero Lorentz axis is missing) (1). If the negative
Lorentz coordinate of `z` vanishes, then `z = 0`. -/
#check (eq_zero_of_negativeCoordinate_eq_zero d hd :
  ∀ z : parametrizedSubspace d, negativeCoordinate d hd z = 0 → z = 0)

/- Lemma 4.12 (The nonzero Lorentz axis is missing) (2). If the negative
Lorentz coordinate of `z` vanishes, then its positive coordinate vanishes. -/
#check (positiveCoordinate_eq_zero_of_negativeCoordinate_eq_zero d hd :
  ∀ z : parametrizedSubspace d,
    negativeCoordinate d hd z = 0 → positiveCoordinate d hd z = 0)

/- Lemma 4.12 (The nonzero Lorentz axis is missing) (3). No point `(p, 0)`
with `p ≠ 0` belongs to the Lorentz embedding range. -/
#check (axis_not_mem_embeddingRange d hd :
  ∀ (p : ℝ), p ≠ 0 → (p, 0) ∉ embeddingRange d hd)

/- Lemma 4.12 (The nonzero Lorentz axis is missing) (4). The ghost point
`(1, 0)` does not belong to the Lorentz embedding range. -/
#check (axis_not_mem_embeddingRange d hd 1 one_ne_zero :
  ghostPoint ∉ embeddingRange d hd)

end Lorentz
