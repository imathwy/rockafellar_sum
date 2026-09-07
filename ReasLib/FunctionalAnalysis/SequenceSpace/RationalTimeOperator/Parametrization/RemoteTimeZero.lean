module

public import ReasLib.Analysis.C0Seq.RemoteBall
public import ReasLib.Analysis.Normed.Group.Approximation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

public section

namespace Lorentz

/-- A parametrized point can have positive Lorentz coordinate zero, first
coordinate in the remote ball, and negative coordinate close to a prescribed
target of norm `1 / 64`. -/
theorem exists_remoteTimeZero (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (nbar : HilbertProd2 UnitL2) (_ : ‖nbar‖ = (1 / 64 : ℝ)) :
    ∃ z₀ : parametrizedSubspace d,
      positiveCoordinate d hd z₀ = 0 ∧
      (z₀ : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖negativeCoordinate d hd z₀ - nbar‖ < (1 / 128 : ℝ) := by
  -- Fix the numerical side conditions before invoking simultaneous approximation.
  have hRadiusPositive : 0 < (1 / 128 : ℝ) := by
    norm_num
  have hRadius_lt_one : (1 / 128 : ℝ) < 1 := by
    norm_num
  -- Prescribe positive coordinate zero and approximate the two remaining targets.
  obtain ⟨z, hzP, hzA, hzN⟩ := exists_approx_fixedPositiveCoordinate d hd h_missing
    0 C0Seq.farPoint (HilbertProd2.fst nbar) (HilbertProd2.snd nbar)
      (1 / 128 : ℝ) hRadiusPositive
  -- The ambient approximation is stronger than membership in the remote unit ball.
  refine ⟨z, hzP, ?_, hzN⟩
  rw [C0Seq.mem_remoteBall]
  simpa only [dist_eq_norm] using lt_trans hzA hRadius_lt_one

/-- The norm of a negative coordinate within `1 / 128` of a target of norm
`1 / 64` lies strictly between zero and `1 / 32`. -/
theorem negativeCoordinate_norm_mem_Ioo (d : C0Seq) (hd : d ≠ 0)
    (nbar : HilbertProd2 UnitL2) (hnbar : ‖nbar‖ = (1 / 64 : ℝ))
    (z₀ : parametrizedSubspace d)
    (happrox : ‖negativeCoordinate d hd z₀ - nbar‖ < (1 / 128 : ℝ)) :
    ‖negativeCoordinate d hd z₀‖ ∈ Set.Ioo 0 (1 / 32 : ℝ) := by
  -- Derive the lower and upper norm bounds from the two triangle inequalities.
  constructor
  · have hnorm : ‖nbar‖ ≤ ‖negativeCoordinate d hd z₀ - nbar‖ +
        ‖negativeCoordinate d hd z₀‖ := by
      calc
        ‖nbar‖ = ‖negativeCoordinate d hd z₀ -
            (negativeCoordinate d hd z₀ - nbar)‖ := by
          rw [sub_sub_cancel]
        _ ≤ ‖negativeCoordinate d hd z₀‖ +
            ‖negativeCoordinate d hd z₀ - nbar‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    -- The approximation radius is smaller than the prescribed target norm.
    rw [hnbar] at hnorm
    nlinarith [norm_nonneg (negativeCoordinate d hd z₀)]
  · have hnorm : ‖negativeCoordinate d hd z₀‖ ≤
        ‖negativeCoordinate d hd z₀ - nbar‖ + ‖nbar‖ := by
      calc
        ‖negativeCoordinate d hd z₀‖ = ‖(negativeCoordinate d hd z₀ - nbar) + nbar‖ := by
          rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    -- Adding the target norm and approximation radius stays below `1 / 32`.
    rw [hnbar] at hnorm
    nlinarith [norm_nonneg (negativeCoordinate d hd z₀)]

/-- At positive Lorentz coordinate zero, the quadratic pairing is the
negative square of the negative-coordinate norm. -/
theorem quadraticPairing_eq_neg_sq_of_timeZero (d : C0Seq) (hd : d ≠ 0)
    (z₀ : parametrizedSubspace d) (hP : positiveCoordinate d hd z₀ = 0) :
    C0Seq.quadraticPairing z₀ = -‖negativeCoordinate d hd z₀‖ ^ 2 := by
  -- Substitute the time-zero coordinate into the Lorentz difference of squares.
  rw [quadraticIdentity d hd z₀, hP]
  ring

/-- A point with positive Lorentz coordinate zero and negative coordinate
within `1 / 128` of a target of norm `1 / 64` has negative quadratic pairing. -/
theorem quadraticPairing_neg_of_timeZero_approx (d : C0Seq) (hd : d ≠ 0)
    (nbar : HilbertProd2 UnitL2) (hnbar : ‖nbar‖ = (1 / 64 : ℝ))
    (z₀ : parametrizedSubspace d) (hP : positiveCoordinate d hd z₀ = 0)
    (happrox : ‖negativeCoordinate d hd z₀ - nbar‖ < (1 / 128 : ℝ)) :
    C0Seq.quadraticPairing z₀ < 0 := by
  -- The approximation estimate makes the negative-coordinate norm strictly positive.
  have hnorm := (negativeCoordinate_norm_mem_Ioo d hd nbar hnbar z₀ happrox).1
  -- Rewrite the pairing as a negative square and use positivity of that square.
  rw [quadraticPairing_eq_neg_sq_of_timeZero d hd z₀ hP]
  nlinarith [sq_pos_of_pos hnorm]

end Lorentz
