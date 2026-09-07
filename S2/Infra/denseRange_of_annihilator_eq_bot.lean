/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.Module.Dual

/-!
# Dense range from a trivial annihilator

This source-facing module records the canonical continuous-dual criterion for
density of an operator range.
-/

public section

universe u v

/- Infrastructure C.7 (Dense range from a trivial continuous annihilator) -/
#check (denseRange_of_annihilator_eq_bot :
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F),
    StrongDual.polarSubmodule ℝ T.range = ⊥ → DenseRange T)
