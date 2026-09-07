module

public import ReasLib.Analysis.Normed.Module.Dual
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator.Triviality

public section

namespace L1Seq

/-- If a vector lies outside the range of the positive operator, then its joint-coordinate map
has dense range. -/
theorem jointCoordinateMap_denseRange
    (d : C0Seq) (h_missing : d ∉ Set.range positiveOperator) :
    DenseRange (jointCoordinateMap d) := by
  -- The Hahn--Banach criterion reduces density to the previously computed annihilator.
  apply denseRange_of_annihilator_eq_bot
  exact jointCoordinateMap_annihilator_eq_bot d h_missing

/-- If `d` lies outside the range of the positive operator, one sequence can simultaneously
approximate prescribed positive, interval, and pairing coordinates. -/
theorem exists_a_approx_target_triple
    (d : C0Seq) (h_missing : d ∉ Set.range positiveOperator)
    (p : ℝ) (x₀ : C0Seq) (v : UnitL2) (r ε : ℝ) (hε : 0 < ε) :
    ∃ a : L1Seq,
      ‖positiveOperator a - ((p + r) • d - x₀)‖ < ε ∧
      ‖intervalCoordinateOperator a - v‖ < ε ∧
      ‖C0Seq.pairingL d a - (p - r)‖ < ε := by
  -- Package the three prescribed coordinates as one point in the product codomain.
  let z : C0Seq × (UnitL2 × ℝ) := ((p + r) • d - x₀, (v, p - r))
  -- Density supplies a sequence whose joint-coordinate image lies in the ε-ball at that point.
  obtain ⟨a, ha⟩ := (jointCoordinateMap_denseRange d h_missing).exists_dist_lt z hε
  -- Expand the product metric once, obtaining a stable maximum bound for all coordinates.
  have ha' :
      max ‖(p + r) • d - x₀ - positiveOperator a‖
          (max ‖v - intervalCoordinateOperator a‖
            ‖(p - r) - C0Seq.pairingL d a‖) < ε := by
    simpa [z, dist_eq_norm, Prod.dist_eq, jointCoordinateMap_apply] using ha
  -- Each coordinate norm is bounded above by the corresponding nested maximum.
  have h₁ : ‖(p + r) • d - x₀ - positiveOperator a‖ < ε :=
    lt_of_le_of_lt (le_max_left _ _) ha'
  have h₂ : ‖v - intervalCoordinateOperator a‖ < ε := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) ha'
  have h₃ : ‖(p - r) - C0Seq.pairingL d a‖ < ε := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) ha'
  -- Reverse the three differences to match the orientations in the conclusion.
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa [norm_sub_rev] using h₁
  · simpa [norm_sub_rev] using h₂
  · simpa [norm_sub_rev] using h₃

end L1Seq
