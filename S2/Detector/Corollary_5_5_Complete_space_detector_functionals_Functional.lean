/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector

/-!
# Detector functional object

This source-facing module records the canonical continuous detector functional
type.
-/

@[expose] public section

#check (Lorentz.detectorFunctional :
  C0Seq → ℕ → ℕ → (C0Seq × L1Seq) →L[ℝ] ℝ)
