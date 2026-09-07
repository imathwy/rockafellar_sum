module

public import ReasLib.Analysis.DyadicDetectorSchedule
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive

public section

namespace Lorentz

/-- A choice of base points in `parametrizedSubspace d` at the folded right-hand times. -/
noncomputable def nearGhostBase (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) :
    ℕ → parametrizedSubspace d :=
  fun i ↦ Classical.choose
    (exists_approx_fixedPositiveCoordinate d hd h_missing
      (DetectorTriple.rightTime i) 0 0 0 (DetectorTriple.rightRadius i / 2)
      (DetectorTriple.rightRadius_half_pos i))

/-- Each selected base point has its prescribed positive coordinate and a
negative coordinate whose norm is less than half the corresponding radius. -/
theorem nearGhostBase_spec (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
    positiveCoordinate d hd (nearGhostBase d hd h_missing i) =
        DetectorTriple.rightTime i ∧
      ‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖ <
        DetectorTriple.rightRadius i / 2 := by
  -- Expose the choice and recover the three guarantees of fixed-time approximation.
  unfold nearGhostBase
  rcases Classical.choose_spec (exists_approx_fixedPositiveCoordinate d hd h_missing
    (DetectorTriple.rightTime i) 0 0 0 (DetectorTriple.rightRadius i / 2)
    (DetectorTriple.rightRadius_half_pos i)) with ⟨hp, _, hn⟩
  refine ⟨hp, ?_⟩
  -- Identify the zero negative-coordinate target with the additive zero.
  have hzero : HilbertProd2.mk (0 : UnitL2) 0 = 0 := by
    apply HilbertProd2.ext
    · rw [HilbertProd2.fst_mk]
      rfl
    · rw [HilbertProd2.snd_mk]
      rfl
  simpa only [hzero, sub_zero] using hn

/-- The positive coordinate of a selected near-ghost base point is its folded time. -/
theorem positiveCoordinate_nearGhostBase (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
    positiveCoordinate d hd (nearGhostBase d hd h_missing i) =
      DetectorTriple.rightTime i := by
  -- Project the exact positive-coordinate guarantee from the choice specification.
  exact (nearGhostBase_spec d hd h_missing i).1

/-- The negative coordinate of a selected near-ghost base point has the prescribed
strict smallness bound. -/
theorem norm_negativeCoordinate_nearGhostBase_lt (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ) :
      ‖negativeCoordinate d hd (nearGhostBase d hd h_missing i)‖ <
      DetectorTriple.rightRadius i / 2 := by
  -- Project the strict negative-coordinate estimate from the choice specification.
  exact (nearGhostBase_spec d hd h_missing i).2

end Lorentz
