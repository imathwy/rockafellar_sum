/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Injective

/-!
# Injectivity of the Psi parametrization

This module records injectivity of the Lorentz parametrization for nonzero directions.
-/

public section

/- Lemma 4.2a (Injectivity of the Ψ parametrization). If `d ≠ 0`, then the
parametrization `Ψ(a, t) = (-Aa + t • d, a)` is injective. -/
#check (Lorentz.parametrization_injective :
  ∀ (d : C0Seq), d ≠ 0 → Function.Injective (Lorentz.parametrization d))
