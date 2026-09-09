/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone
public import ReasLib.Analysis.Normed.LorentzCone.PolarDivergence

/-!
# Polar-carrier exclusion interface

This is the logical shell of the detector argument proving that a monotone
polar is contained in a carrier.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- Divergent quadratic witnesses exclude every point outside a carrier from
the monotone polar of a seed set. -/
theorem monotonePolar_subset_of_divergent_witnesses
    (P : DualPairing X Xstar) (S C : Set (X × Xstar))
    (hdiv : ∀ w, w ∉ C →
      ∃ f : ℕ → (X × Xstar),
        (∀ n, f n ∈ S) ∧
        Filter.Tendsto (fun n ↦ P.quadratic (w - f n))
          Filter.atTop Filter.atBot) :
    P.monotonePolar S ⊆ C := by
  intro w hw
  by_contra hwC
  obtain ⟨f, hfS, hfdiv⟩ := hdiv w hwC
  rw [P.mem_monotonePolar] at hw
  have hbound : ∀ n, 0 ≤ P.quadratic (w - f n) := by
    intro n
    exact hw (f n) (hfS n)
  have hev := Filter.tendsto_atBot.1 hfdiv (-1 : ℝ)
  have hevFalse : ∀ᶠ n in Filter.atTop, False :=
    hev.mono (fun n hn => by linarith [hbound n])
  exact (Filter.Eventually.exists hevFalse).choose_spec

end DualPairing
