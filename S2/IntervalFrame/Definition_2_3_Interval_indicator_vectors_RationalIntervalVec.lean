module

public import ReasLib.MeasureTheory.UnitL2.RationalIntervalIndicator

open MeasureTheory

#check (UnitL2.rationalIntervalVec : ℕ → UnitL2)
#check (UnitL2.rationalIntervalVec_apply_ae :
  ∀ n : ℕ,
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      UnitL2.rationalIntervalVec n x =
        (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) x)
