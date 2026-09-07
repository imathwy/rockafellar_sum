module

public import ReasLib.Analysis.DyadicDetectorSchedule

public section

/- Construction 6.8 (Repeated signed detector schedule) (1): `DetectorTriple`
encodes the ordered coordinates and sign, while `schedule` repeats every triple
infinitely often. -/
#check (DetectorTriple : Type)
#check
  (DetectorTriple.p_lt_q :
    ∀ t : DetectorTriple, DetectorTriple.p t < DetectorTriple.q t)
#check (DetectorTriple.schedule : RepeatingSchedule DetectorTriple)
#check
  (DetectorTriple.schedule_infinite_fiber :
    ∀ t : DetectorTriple,
      Set.Infinite {i | DetectorTriple.schedule.toFun i = t})
#check
  (DetectorTriple.coe_sign_eq_neg_one_or_one :
    ∀ t : DetectorTriple,
      (DetectorTriple.sign t : ℝ) = -1 ∨
        (DetectorTriple.sign t : ℝ) = 1)

/- Construction 6.8 (Repeated signed detector schedule) (2): for zero-based `i`,
the right-hand detector time is `1 + 2 ^ (-(i + 1 : ℝ))`. -/
#check
  (DetectorTriple.rightTime_def :
    ∀ i : ℕ, DetectorTriple.rightTime i =
      1 + (2 : ℝ) ^ (-(i + 1 : ℝ)))

/- Construction 6.8 (Repeated signed detector schedule) (3): for zero-based `i`,
the right-hand detector radius is `2 ^ (-(i + 6 : ℝ))`. -/
#check
  (DetectorTriple.rightRadius_def :
    ∀ i : ℕ, DetectorTriple.rightRadius i =
      (2 : ℝ) ^ (-(i + 6 : ℝ)))
