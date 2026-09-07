/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Dual

/-!
# Dual Isometry

This module exposes the canonical isometric equivalence between `C0Seq` duals and `L1Seq`.
-/

#check (C0Seq.dualEquivL1 : StrongDual ℝ C0Seq ≃ₗᵢ[ℝ] L1Seq)
