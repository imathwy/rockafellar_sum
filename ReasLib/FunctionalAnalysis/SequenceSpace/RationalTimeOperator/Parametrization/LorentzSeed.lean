/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedSet

/-!
# Lorentz seed template on the parametrized carrier
-/

public section

namespace Lorentz

/-- The half-line component `γ(p) = z₀ + p • v`, restricted to `p ≤ 1 / 2`. -/
def seedHalfLine (d : C0Seq) (z₀ v : parametrizedSubspace d) :
    Set (C0Seq × L1Seq) :=
  Set.range (fun p : {p : ℝ // p ≤ 1 / 2} =>
    ((z₀ + p.1 • v : parametrizedSubspace d) : C0Seq × L1Seq))

/-- The complete Lorentz seed template. -/
def lorentzSeed (d : C0Seq) (z₀ v : parametrizedSubspace d)
    (detectors : Set (C0Seq × L1Seq)) : Set (C0Seq × L1Seq) :=
  seedHalfLine d z₀ v ∪ detectors ∪
    {((2 • v : parametrizedSubspace d) : C0Seq × L1Seq)}

/-- The half-line component of a Lorentz seed lies in its parametrized carrier. -/
theorem seedHalfLine_subset_carrier (d : C0Seq) (z₀ v : parametrizedSubspace d) :
    seedHalfLine d z₀ v ⊆ parametrizedSubspace d := by
  intro z hz
  rcases hz with ⟨p, rfl⟩
  exact (z₀ + p.1 • v).property

/-- The full Lorentz seed lies in the parametrized carrier whenever its detector
component does. -/
theorem lorentzSeed_subset_carrier (d : C0Seq) (z₀ v : parametrizedSubspace d)
    (detectors : Set (C0Seq × L1Seq))
    (hdet : detectors ⊆ parametrizedSubspace d) :
    lorentzSeed d z₀ v detectors ⊆ parametrizedSubspace d := by
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · exact seedHalfLine_subset_carrier d z₀ v hz
    · exact hdet hz
  · rcases hz with rfl
    exact (2 • v : parametrizedSubspace d).property

end Lorentz
