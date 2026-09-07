/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteCopySequence

/-!
# Remote-detector difference sequence

This source-facing module records the canonical remote-detector difference
map and its pointwise formula.
-/

#check (L1Seq.remoteDetectorDifference :
  C0Seq → ℕ → ℕ → (ℕ → L1Seq) → ℕ → L1Seq)

#check (L1Seq.remoteDetectorDifference_apply :
  ∀ (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    L1Seq.remoteDetectorDifference d p q c n = L1Seq.twoDet d p q - c n)
