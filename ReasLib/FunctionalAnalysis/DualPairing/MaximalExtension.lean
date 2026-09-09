/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.DualPairing.Monotone
public import Mathlib.Order.Zorn

/-!
# Maximal monotone extensions

This module provides the Zorn extension used by the seed-set reduction.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- Every monotone subset of a dual-pairing product is contained in a maximal
monotone subset. -/
theorem exists_maximal_monotone_superset (P : DualPairing X Xstar)
    {S : Set (X × Xstar)} (hS : P.IsMonotone S) :
    ∃ G, S ⊆ G ∧ Maximal P.IsMonotone G := by
  let family : Set (Set (X × Xstar)) := {T | P.IsMonotone T}
  have hfamily : P.IsMonotone S := hS
  obtain ⟨G, hSG, hG⟩ := zorn_subset_nonempty family
      (show S ∈ family from hfamily)
      (by
        intro c hc hchain hne
        refine ⟨⋃₀ c, ?_, ?_⟩
        · intro z hz w hw
          rcases Set.mem_sUnion.mp hz with ⟨T, hTc, hzT⟩
          rcases Set.mem_sUnion.mp hw with ⟨U, hUc, hwU⟩
          rcases hchain.total hTc hUc with hTU | hUT
          · exact (hc hTc) z hzT w (hTU hwU)
          · exact (hc hUc) z (hUT hzT) w hwU
        · exact Set.mem_sUnion_of_mem (Classical.choice hne) (hc (Classical.choice hne)) )
  exact ⟨G, hSG, hG⟩

end DualPairing
