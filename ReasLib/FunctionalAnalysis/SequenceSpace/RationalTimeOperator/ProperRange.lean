/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.StrongDual
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.PositiveDefinite
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Transpose.C0Range

/-!
# Proper range of the positive operator

This module records the nonsurjectivity of the rational-time positive operator
on `L1Seq`.
-/

namespace L1Seq

/-- The rational-time positive operator on real summable sequences is not surjective. -/
public theorem positiveOperator_not_surjective :
    ¬ Function.Surjective positiveOperator := by
  -- Local instance justification (proof-local temporary data): the abstract
  -- transpose criterion needs only a witness that `C0Seq` is nontrivial.
  letI : Nontrivial C0Seq := by
    refine ⟨⟨0, c0Single 0 1, ?_⟩⟩
    intro h
    have hcoord := congrArg (fun x : C0Seq => x 0) h
    simp at hcoord
  -- Reduce nonsurjectivity to the trivial intersection of the transpose image
  -- with the canonical copy of `C0Seq` in the strong dual.
  apply ContinuousLinearMap.not_surjective_of_transpose_transverse
    positiveOperator C0Seq.pairingL
  · exact positiveOperator_injective
  · exact C0Seq.pairingL_injective
  · intro b h_transpose
    let b' : L1Seq := C0Seq.dualEquivL1 b
    -- Express raw precomposition in the reindexed-transpose coordinates.
    have h_eq : positiveOperator.reindexedTranspose b' =
        ContinuousLinearMap.precomp ℝ positiveOperator b := by
      rw [ContinuousLinearMap.reindexedTranspose_apply]
      have hpaper : positiveOperator.paperTranspose b =
          ContinuousLinearMap.precomp ℝ positiveOperator b := by
        ext a
        rw [ContinuousLinearMap.paperTranspose_apply,
          ContinuousLinearMap.precomp_apply]
        rfl
      have hbdual : C0Seq.dualEquivL1.symm b' = b := by
        simp [b']
      rw [hbdual, hpaper]
    -- Transversality forces the reindexed dual vector to vanish.
    have hb' : b' = 0 := by
      apply positiveOperator_reindexedTranspose_transverse b'
      rw [h_eq]
      exact h_transpose
    -- Injectivity of the dual equivalence transports this vanishing back to `b`.
    apply C0Seq.dualEquivL1.injective
    change b' = C0Seq.dualEquivL1 0
    rw [hb']
    exact (C0Seq.dualEquivL1.map_zero).symm

end L1Seq
