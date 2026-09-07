module

import ReasLib.MeasureTheory.UnitL2.RationalIntervalIndicator

open MeasureTheory

/- Definition 2.3 (Interval indicator vectors) (1): the interval-indicator family `u_t`. -/
#check (UnitL2.intervalVec : unitInterval → UnitL2)
#check (UnitL2.intervalVec_apply_ae :
  ∀ t : unitInterval,
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      UnitL2.intervalVec t x =
        (Set.Ioo (0 : ℝ) t).indicator (fun _ ↦ (1 : ℝ)) x)

/- Definition 2.3 (Interval indicator vectors) (2): the sequence `u_n = u_{t_n}`. -/
#check (UnitL2.rationalIntervalVec : ℕ → UnitL2)
#check (UnitL2.rationalIntervalVec_apply_ae :
  ∀ n : ℕ,
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      UnitL2.rationalIntervalVec n x =
        (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) x)
