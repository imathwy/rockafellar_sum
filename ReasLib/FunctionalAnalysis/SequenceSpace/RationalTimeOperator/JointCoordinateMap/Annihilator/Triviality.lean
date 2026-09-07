/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.Annihilator.Elimination

/-!
# Triviality of the joint-coordinate annihilator

This module proves that a missing positive-operator direction forces the joint
coordinate annihilator to be trivial.
-/

public section

namespace L1Seq

/-- If a vector lies outside the range of the positive operator, then the continuous
annihilator of the range of its joint-coordinate map is trivial. -/
theorem jointCoordinateMap_annihilator_eq_bot
    (d : C0Seq) (h_missing : d ∉ Set.range positiveOperator) :
    StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range = ⊥ := by
  -- Reduce equality with the bottom submodule to vanishing of each annihilating functional.
  apply le_antisymm
  · intro φ hφ
    -- Decompose `φ` into the canonical dual coordinates of the finite product.
    have h_repr :
        (ContinuousLinearMap.dualProdMap (𝕜 := ℝ) (E := C0Seq) (F := UnitL2))
            ((ContinuousLinearMap.dualProdCoords (𝕜 := ℝ) (E := C0Seq) (F := UnitL2)) φ) = φ :=
      ContinuousLinearMap.dualProdMap_dualProdCoords φ
    rcases h_coords :
        (ContinuousLinearMap.dualProdCoords (𝕜 := ℝ) (E := C0Seq) (F := UnitL2)) φ with
      ⟨b, y, lam⟩
    have h_ann :
        ContinuousLinearMap.dualProdMap (b, y, lam) ∈
          StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range := by
      rw [← h_coords, h_repr]
      exact hφ
    -- Transport the first two dual coordinates through the standard `L1Seq`
    -- and Riesz identifications.
    let b' : L1Seq := C0Seq.dualEquivL1 b
    let y' : UnitL2 := (InnerProductSpace.toDual ℝ UnitL2).symm y
    have h_ann' :
        ContinuousLinearMap.dualProdMap
            (C0Seq.dualEquivL1.symm b', (InnerProductSpace.toDual ℝ UnitL2) y', lam) ∈
          StrongDual.polarSubmodule ℝ (jointCoordinateMap d).range := by
      simpa [b', y'] using h_ann
    -- The annihilator equation and the missing-range hypothesis force all coordinates to vanish.
    have h_zero :=
      jointCoordinateMap_annihilator_eq_zero d h_missing b' y' lam
        ((jointCoordinateMap_annihilator_iff d b' y' lam).1 h_ann')
    have hb' : b' = 0 := by
      simpa using congrArg Prod.fst h_zero
    have hy' : y' = 0 := by
      simpa using congrArg (fun q : L1Seq × (UnitL2 × ℝ) => q.2.1) h_zero
    have hlam : lam = 0 := by
      simpa using congrArg (fun q : L1Seq × (UnitL2 × ℝ) => q.2.2) h_zero
    -- Pull the zero coordinates back through both equivalences.
    have hb : b = 0 := by
      apply C0Seq.dualEquivL1.injective
      change b' = C0Seq.dualEquivL1 0
      rw [hb']
      exact (C0Seq.dualEquivL1.map_zero).symm
    have hy : y = 0 := by
      calc
        y = (InnerProductSpace.toDual ℝ UnitL2) y' := by
          exact (InnerProductSpace.toDual ℝ UnitL2).apply_symm_apply y |>.symm
        _ = (InnerProductSpace.toDual ℝ UnitL2) 0 := by rw [hy']
        _ = 0 := (InnerProductSpace.toDual ℝ UnitL2).map_zero
    -- Reconstruct `φ` from its coordinates and conclude membership in the bottom submodule.
    have hφ_zero : φ = 0 := by
      calc
        φ = ContinuousLinearMap.dualProdMap (b, y, lam) := by
          rw [← h_coords]
          exact h_repr.symm
        _ = 0 := by
          rw [hb, hy, hlam]
          change ContinuousLinearMap.dualProdMap
            (0 : StrongDual ℝ C0Seq × (StrongDual ℝ UnitL2 × ℝ)) = 0
          exact map_zero _
    exact (Submodule.mem_bot ℝ).2 hφ_zero
  · exact bot_le

end L1Seq
