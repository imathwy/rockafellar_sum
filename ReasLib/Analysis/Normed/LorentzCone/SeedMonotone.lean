/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.LorentzCone.SeedTemplate

/-!
# Monotonicity interface for Lorentz seeds

The concrete seed construction is reduced to a pairwise Lipschitz estimate in
Lorentz coordinates. This is the formal counterpart of the five pair cases in
the technical report.
-/

@[expose] public section

universe u

namespace Lorentz

/-- A set of Lorentz points satisfies the pairwise seed estimate when its
negative coordinate is 1-Lipschitz in the positive coordinate. -/
def PairwiseSeedLipschitz {H : Type u} [SeminormedAddCommGroup H]
    (S : Set (ℝ × H)) : Prop :=
  ∀ z ∈ S, ∀ w ∈ S, ‖z.2 - w.2‖ ≤ |z.1 - w.1|

/-- Pairwise seed estimates imply nonnegative Lorentz energy for every
difference of seed points. -/
theorem energy_nonneg_sub_of_pairwiseSeedLipschitz {H : Type u}
    [SeminormedAddCommGroup H] {S : Set (ℝ × H)}
    (hS : PairwiseSeedLipschitz S) {z w : ℝ × H}
    (hz : z ∈ S) (hw : w ∈ S) :
    0 ≤ energy (z.1 - w.1, z.2 - w.2) := by
  apply energy_nonneg_of_norm_sub_le_abs_sub
  exact hS z hz w hw

/-- The Lorentz seed estimate is symmetric in the two points. -/
theorem pairwiseSeedLipschitz_comm {H : Type u} [SeminormedAddCommGroup H]
    {S : Set (ℝ × H)} (hS : PairwiseSeedLipschitz S) :
    ∀ z ∈ S, ∀ w ∈ S, ‖w.2 - z.2‖ ≤ |w.1 - z.1| := by
  intro z hz w hw
  simpa only [norm_neg, abs_neg, sub_eq_add_neg] using hS w hw z hz

end Lorentz
