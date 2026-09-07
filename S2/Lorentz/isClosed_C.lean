/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.ClosedRange

/-!
# Closedness of the parametrized subspace

This module records closedness of the range of the Lorentz parametrization away
from the zero direction.
-/

public section

/-
Lemma 4.2c (Closedness of the parametrized range): if `d ≠ 0`, then the
subspace parametrized by `Ψ(a, t) = (-Aa + t • d, a)` is closed.
-/
#check (Lorentz.isClosed_parametrizedSubspace : ∀ (d : C0Seq), d ≠ 0 →
  IsClosed (Lorentz.parametrizedSubspace d : Set (C0Seq × L1Seq)))
