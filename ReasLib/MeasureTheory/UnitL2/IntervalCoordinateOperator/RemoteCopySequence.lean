/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.TwoCoordinateDeterminant
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Relocation

/-!
# Remote copies of determinant vectors

This module constructs equal-norm remote copies whose interval-coordinate
images converge to the original determinant vector.
-/

public section

namespace L1Seq

/-- For two ordered coordinates, there is a sequence of equal-norm copies of the
associated determinant vector, supported successively farther out, whose
interval-coordinate images converge with error bounded by `1 / (n + 1 : ℝ)`. -/
theorem exists_remoteDetectorCopy (d : C0Seq) (p q : ℕ) (_ : p < q) :
    ∃ c : ℕ → L1Seq, ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖twoDet d p q‖ ∧
        ‖intervalCoordinateOperator (c n) - intervalCoordinateOperator (twoDet d p q)‖ <
          1 / (n + 1 : ℝ) := by
  classical
  -- Each reciprocal tolerance is strictly positive, including at the initial cutoff.
  have hTolerancePositive (n : ℕ) : 0 < 1 / (n + 1 : ℝ) := by
    positivity
  -- Remote replication gives a suitable detector copy separately at every cutoff.
  have hRemoteCopyAtCutoff (n : ℕ) :
      ∃ b' : L1Seq,
        Function.support (fun m ↦ b' m) ⊆ Set.Ioi n ∧
          ‖b'‖ = ‖twoDet d p q‖ ∧
          ‖intervalCoordinateOperator b' - intervalCoordinateOperator (twoDet d p q)‖ <
            1 / (n + 1 : ℝ) := by
    exact exists_remoteReplication (twoDet d p q) (twoDet_hasFiniteSupport d p q)
      n (1 / (n + 1 : ℝ)) (hTolerancePositive n)
  -- Countable choice assembles the pointwise remote copies into the required sequence.
  choose c hc using hRemoteCopyAtCutoff
  exact ⟨c, hc⟩

/-- The difference between a two-coordinate detector and an explicitly supplied
sequence of remote copies. -/
noncomputable def remoteDetectorDifference (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) :
    ℕ → L1Seq :=
  fun n ↦ twoDet d p q - c n

/-- Evaluation of the remote-detector difference sequence at an index. -/
theorem remoteDetectorDifference_apply (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    remoteDetectorDifference d p q c n = twoDet d p q - c n := by
  -- Unfolding the difference sequence exposes the defining pointwise subtraction.
  rfl

end L1Seq
