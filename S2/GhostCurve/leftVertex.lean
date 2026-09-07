/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex

/-!
# Selected left vertices

This module exposes the simultaneous choice specification for left dyadic
vertices.
-/

public section

/- Lemma 6.4b (Simultaneous choice of left vertices) -/
#check (Lorentz.leftVertex_spec :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (z₀ : Lorentz.parametrizedSubspace d) (k : ℕ),
    Lorentz.positiveCoordinate d hd (Lorentz.leftVertex d hd h_missing z₀ k) =
        Lorentz.leftTime k ∧
      (Lorentz.leftVertex d hd h_missing z₀ k : C0Seq × L1Seq).1 ∈
          C0Seq.remoteBall ∧
      ‖Lorentz.negativeCoordinate d hd (Lorentz.leftVertex d hd h_missing z₀ k) -
          Lorentz.leftTemplate (Lorentz.negativeCoordinate d hd z₀) (Lorentz.leftTime k)‖ <
        Lorentz.leftRadius k)
