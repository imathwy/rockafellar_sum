/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.FiniteProductDual

/-!
# Continuous dual of a finite product

This source-facing module records the canonical coordinate decomposition of a
continuous functional on a three-factor product.
-/

public section

/- Infrastructure A.13 (Continuous dual of a finite product)
Every continuous linear functional on `E × (F × ℝ)` decomposes uniquely into
coordinate functionals, and evaluation is the sum of the three coordinate evaluations. -/
#check (ContinuousLinearMap.existsUnique_dualProd :
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : StrongDual ℝ (E × (F × ℝ))),
    ∃! p : StrongDual ℝ E × (StrongDual ℝ F × ℝ),
      ∀ x y t, L (x, y, t) = p.1 x + p.2.1 y + p.2.2 * t)
