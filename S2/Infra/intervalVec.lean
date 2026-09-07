module

import ReasLib.MeasureTheory.UnitL2.IntervalIndicator

/- Infrastructure B.2 (Interval indicators as L² vectors) -/
#check (UnitL2.intervalVec : unitInterval → UnitL2)
#check (UnitL2.intervalVec_apply_ae :
  ∀ t : unitInterval,
    ∀ᵐ x : ℝ ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
      UnitL2.intervalVec t x =
        (Set.Ioo (0 : ℝ) t).indicator (fun _ ↦ (1 : ℝ)) x)
