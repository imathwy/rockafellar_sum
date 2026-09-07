module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding
public import ReasLib.Analysis.Normed.LorentzCone

public section

namespace Lorentz

/-- A scalar multiple of a normalized parametrized point gives its displayed
Lorentz-coordinate point in the range of the Lorentz embedding. -/
theorem futureRay_mem_embeddingRange (d : C0Seq) (hd : d ≠ 0)
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (P : ℝ) (_ : 2 ≤ P) :
    (P, negativeCoordinate d hd (P • v)) ∈ embeddingRange d hd := by
  -- Use the scaled parametrized point itself as the range witness.
  rw [mem_embeddingRange]
  refine ⟨P • v, ?_⟩
  rw [embedding_apply]
  -- Linearity and the normalization `positiveCoordinate v = 1` identify both coordinates.
  apply Prod.ext
  · rw [map_smul, hvP]
    simp only [smul_eq_mul, mul_one]
  · rfl

/-- The negative coordinate of a normalized future-ray base vector has norm
strictly less than one. -/
theorem futureRay_slope_lt_one (d : C0Seq) (hd : d ≠ 0)
    (v : parametrizedSubspace d)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16) :
    ‖negativeCoordinate d hd v‖ < 1 := by
  -- The imported `1 / 16` estimate is strictly stronger than the desired unit bound.
  linarith

/-- Along a normalized future ray at scale `P ≥ 2`, the negative coordinate
has norm below `P / 16`, and `P / 16` is at most `P - 1`. -/
theorem futureRay_negativeCoordinate_bounds (d : C0Seq) (hd : d ≠ 0)
    (v : parametrizedSubspace d)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : 2 ≤ P) :
    ‖negativeCoordinate d hd (P • v)‖ < P / 16 ∧ P / 16 ≤ P - 1 := by
  -- Positivity of the scale turns the norm of the scalar into `P` itself.
  have hPpos : 0 ≤ P := by linarith
  have hnorm : ‖negativeCoordinate d hd (P • v)‖ =
      P * ‖negativeCoordinate d hd v‖ := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hPpos]
  -- Scale the strict base estimate, then discharge the remaining scalar inequality.
  constructor
  · rw [hnorm]
    have hmul := mul_lt_mul_of_pos_left hvN (by linarith : 0 < P)
    nlinarith
  · nlinarith

/-- The Lorentz embedding of a normalized future-ray point at scale `P ≥ 2`
belongs to the future Lorentz cone. -/
theorem futureRay_mem_futureCone (d : C0Seq) (hd : d ≠ 0)
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : 2 ≤ P) :
    embedding d hd (P • v) ∈ futureCone (HilbertProd2 UnitL2) := by
  -- Reduce cone membership to the defining coordinate inequality.
  rw [embedding_apply, mem_futureCone]
  change ‖negativeCoordinate d hd (P • v)‖ ≤ positiveCoordinate d hd (P • v)
  have hcoord : positiveCoordinate d hd (P • v) = P := by
    rw [map_smul, hvP]
    simp only [smul_eq_mul, mul_one]
  rw [hcoord]
  -- The sharp `P / 16` estimate is stronger than the required bound by `P`.
  have hbounds := futureRay_negativeCoordinate_bounds d hd v hvN P hP
  exact (calc
    ‖negativeCoordinate d hd (P • v)‖ < P / 16 := hbounds.1
    _ ≤ P - 1 := hbounds.2
    _ ≤ P := by linarith).le

/-- The Lorentz embedding of a normalized future-ray point at scale `P ≥ 2`
has nonnegative Lorentz energy. -/
theorem futureRay_energy_nonneg (d : C0Seq) (hd : d ≠ 0)
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : 2 ≤ P) :
    0 ≤ energy (embedding d hd (P • v)) := by
  -- Project nonnegativity of Lorentz energy from the established future-cone membership.
  exact energy_nonneg_of_mem_futureCone
    (futureRay_mem_futureCone d hd v hvP hvN P hP)

/-- Doubling a parametrized point whose primal coordinate has norm below
`1 / 8` produces a primal coordinate with norm below `1 / 4`. -/
theorem norm_two_smul_primal_lt_quarter
    (d : C0Seq) (v : parametrizedSubspace d)
    (hvX : ‖v.1.1‖ < (1 : ℝ) / 8) :
    ‖((2 : ℝ) • v).1.1‖ < (1 : ℝ) / 4 := by
  have hnorm : ‖((2 : ℝ) • v).1.1‖ = 2 * ‖v.1.1‖ := by
    rw [Submodule.coe_smul, Prod.smul_fst, norm_smul, Real.norm_eq_abs]
    norm_num
  rw [hnorm]
  nlinarith

end Lorentz
