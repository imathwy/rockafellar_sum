/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Realization

/-!
# Non-ghost points lie in the embedding range

This module records that every non-ghost curve point is an actual embedded point.
-/

/- Lemma 6.19 (Every non-ghost curve point is an actual point of $E$): with
`E = Lorentz.embeddingRange d hd` and `f = Lorentz.ghostCurveN ...`, every
`P ≠ 1` gives `(P, f P) ∈ E`. -/
#check Lorentz.ghostCurveN_mem_embeddingRange
