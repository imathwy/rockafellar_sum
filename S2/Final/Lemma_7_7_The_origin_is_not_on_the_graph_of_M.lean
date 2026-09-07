/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing.Origin
public import S2.Final.Definition_7_1_The_ghost_curve_operator_M_Operator

/-!
# The origin is not on the operator graph

This module records the exclusion of the origin from the monotone ghost-curve graph.
-/

public section

namespace Lorentz

variable (d : C0Seq) (hd : d ≠ 0)
  (h_missing : d ∉ Set.range L1Seq.positiveOperator)
  (zLeft z₀ : parametrizedSubspace d)
  (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
  (h_tendsto : ∀ p q (h_pq : p < q),
    Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
      Filter.atTop (nhds 0))
  (v : parametrizedSubspace d)

/- Lemma 7.7 (The origin is not on the graph of $M$)
A negative-quadratic point on the monotone ghost-curve graph excludes the origin. -/
#check (C0Seq.zero_not_mem_of_quadraticPairing_neg
    (S := (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (z := (z₀ : C0Seq × L1Seq)) :
  (z₀ : C0Seq × L1Seq) ∈
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph →
    C0Seq.quadraticPairing z₀ < 0 →
      C0Seq.coordinateDualPairing.IsMonotone
          (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph →
        (0, 0) ∉
          (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)

end Lorentz
