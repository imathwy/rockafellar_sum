/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.LorentzCone.SeedTemplate

/-!
# Scaled detector divergence estimates
-/

public section

namespace Lorentz

/-- A nonpositive detector energy and a positive linear pairing force the
scaled Lorentz energy below a linear negative bound. -/
theorem energy_scaled_le_of_nonpos_direction
    {q c e r η : ℝ} (hr : 0 ≤ r) (he : e ≤ 0) (hc : η ≤ c) (hη : 0 ≤ η) :
    q - 2 * r * c + r ^ 2 * e ≤ q - 2 * r * η := by
  have hrc : 2 * r * η ≤ 2 * r * c := by
    nlinarith
  have hre : r ^ 2 * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) he
  linarith

end Lorentz
