module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.Realization
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay
public import ReasLib.Analysis.C0Seq.Localization

public section

namespace Lorentz

/-- Twice a normalized future-ray base point with sufficiently small primal
coordinate lies in the ghost-curve operator domain and in the interior of the
fixed constraint set. -/
theorem two_smul_primal_mem_constraintQualification
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvX : ‖v.1.1‖ < (1 : ℝ) / 8) :
    ((2 : ℝ) • v).1.1 ∈
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).dom ∩
        interior C0Seq.finalConstraint := by
  constructor
  · exact two_smul_primal_mem_ghostCurveOperator_dom d hd h_missing zLeft z₀ h
      h_tendsto v hvP
  · change ((2 : ℝ) • v).1.1 ∈ interior (Metric.closedBall (0 : C0Seq) (1 / 2))
    apply Metric.ball_subset_interior_closedBall
    rw [Metric.mem_ball, dist_zero_right]
    change ‖(2 : ℝ) • (v : C0Seq × L1Seq).1‖ < (1 : ℝ) / 2
    rw [norm_smul]
    norm_num [Real.norm_eq_abs]
    linarith

/-- The ghost-curve operator domain meets the interior of the fixed constraint
set whenever its normalized future-ray base point has sufficiently small
primal coordinate. -/
theorem ghostCurveOperator_constraintQualification
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvX : ‖v.1.1‖ < (1 : ℝ) / 8) :
    Set.Nonempty
      ((ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).dom ∩
        interior C0Seq.finalConstraint) := by
  refine ⟨((2 : ℝ) • v).1.1, ?_⟩
  exact two_smul_primal_mem_constraintQualification d hd h_missing zLeft z₀ h
    h_tendsto v hvP hvX

end Lorentz
