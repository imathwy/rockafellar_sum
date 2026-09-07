/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.NearGhostBase

/-!
# Near-ghost base-point API

This module exposes the selected base points at folded detector times and their
specification formulas.
-/

public section

#check (Lorentz.nearGhostBase :
  (d : C0Seq) → d ≠ 0 → d ∉ Set.range L1Seq.positiveOperator →
    ℕ → Lorentz.parametrizedSubspace d)

#check (DetectorTriple.rightTime_def :
  ∀ i : ℕ, DetectorTriple.rightTime i = 1 + (2 : ℝ) ^ (-(i + 1 : ℝ)))

#check (DetectorTriple.rightRadius_def :
  ∀ i : ℕ, DetectorTriple.rightRadius i = (2 : ℝ) ^ (-(i + 6 : ℝ)))

/- Lemma 6.9a (Choice of small-N base points at folded times): for every zero-based
index `i`, the selected point has the prescribed dyadic positive coordinate and its
negative-coordinate norm is less than half the prescribed dyadic radius. -/
#check (Lorentz.nearGhostBase_spec :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ),
    Lorentz.positiveCoordinate d hd (Lorentz.nearGhostBase d hd h_missing i) =
        DetectorTriple.rightTime i ∧
      ‖Lorentz.negativeCoordinate d hd (Lorentz.nearGhostBase d hd h_missing i)‖ <
        DetectorTriple.rightRadius i / 2)
