/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Topology.RationalTime

/-!
# Divergence interface for polar exclusion

The seed polar argument only needs the following elementary order-theoretic
fact: a polar inequality supplies a fixed upper bound, while detector points
make the same expression diverge.
-/

public section

open Filter Topology

/-- A sequence which eventually exceeds every fixed bound cannot satisfy a
uniform upper bound. -/
theorem not_forall_le_of_tendsto_atTop {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (b : ℝ) : ¬ (∀ n, f n ≤ b) := by
  intro hbound
  have hev : ∀ᶠ n in atTop, b + 1 ≤ f n :=
    tendsto_atTop.1 hf (b + 1)
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  have hlarge : b + 1 ≤ f N := hN N le_rfl
  linarith [hbound N]

/-- Polar exclusion in its scalar form: a point is excluded whenever detector
values minus seed energies diverge to positive infinity. -/
theorem mem_polar_false_of_detector_divergence
    {f : ℕ → ℝ} {bound : ℝ}
    (hpolar : ∀ n, f n ≤ bound)
    (hdiv : Tendsto f atTop atTop) : False := by
  exact (not_forall_le_of_tendsto_atTop hdiv bound) hpolar

end
