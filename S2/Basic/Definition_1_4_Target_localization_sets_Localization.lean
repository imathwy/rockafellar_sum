/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.Localization

/-!
# Localization-set objects

This source-facing module records the canonical local open ball and final
closed-ball constraint.
-/

open scoped ZeroAtInfty

#check (C0Seq.localOpenUnitBall : Set C₀(ℕ, ℝ))
#check (C0Seq.finalConstraint : Set C₀(ℕ, ℝ))
