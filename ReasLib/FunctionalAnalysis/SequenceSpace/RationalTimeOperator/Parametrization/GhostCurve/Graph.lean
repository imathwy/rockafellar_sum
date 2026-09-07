/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Data.Set.Prod
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding

/-!
# Ghost-curve graph

This module defines the ambient graph of the parametrized ghost curve and its
coordinate membership API.
-/

public section

namespace Lorentz

variable (d : C0Seq) (hd : d ≠ 0)
variable (h_missing : d ∉ Set.range L1Seq.positiveOperator)
variable (zLeft z₀ : parametrizedSubspace d)
variable (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
variable (h_tendsto : ∀ p q (h_pq : p < q),
  Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
    Filter.atTop (nhds 0))
variable (v : parametrizedSubspace d)

/-- The ambient graph consists of the parametrized points whose positive
coordinate is not the ghost time and whose negative coordinate lies on
`ghostCurveN`. -/
noncomputable def ghostGraph : Set (C0Seq × L1Seq) :=
  Subtype.val '' {z : parametrizedSubspace d |
    positiveCoordinate d hd z ≠ 1 ∧
      negativeCoordinate d hd z =
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd z)}

/-- Membership in `ghostGraph` is equivalent to its direct coordinate predicate. -/
@[simp]
theorem mem_ghostGraph (z : parametrizedSubspace d) :
    z.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v ↔
      positiveCoordinate d hd z ≠ 1 ∧
        negativeCoordinate d hd z =
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
            (positiveCoordinate d hd z) := by
  unfold ghostGraph
  constructor
  · rintro ⟨z', hz', hval⟩
    have hzeq : z' = z := Subtype.ext hval
    simpa [hzeq] using hz'
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The graph is the ambient image of the relational preimage of the restricted
coordinate graph under the Lorentz embedding. -/
theorem ghostGraph_eq_preimage_graphOn :
    ghostGraph d hd h_missing zLeft z₀ h h_tendsto v =
      Subtype.val '' ((embedding d hd) ⁻¹'
        Set.graphOn (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
          {P : ℝ | P ≠ 1}) := by
  ext p
  constructor
  · intro hp
    unfold ghostGraph at hp
    rcases hp with ⟨z, hz, hpz⟩
    refine ⟨z, ?_, hpz⟩
    rw [Set.mem_preimage, Set.mem_graphOn]
    rw [embedding_apply]
    exact ⟨hz.1, hz.2.symm⟩
  · intro hp
    rcases hp with ⟨z, hz, hpz⟩
    unfold ghostGraph
    refine ⟨z, ?_, hpz⟩
    rw [Set.mem_preimage, Set.mem_graphOn] at hz
    rw [embedding_apply] at hz
    exact ⟨hz.1, hz.2.symm⟩

end Lorentz
