/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve

/-!
# The assembled ghost curve

This module exposes the piecewise global negative-coordinate curve and its branch formulas.
-/

public section

/- Definition 6.18a (Piecewise definition of the global N-coordinate curve):
the total negative-coordinate curve is assembled from the past ray, affine bridges,
left and right dyadic edges, the ghost value at time one, and the future ray. -/
#check (Lorentz.ghostCurveN :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d) (P : ℝ),
    HilbertProd2 UnitL2)

#check Lorentz.leftEdgeIndex
#check Lorentz.leftEdgeIndex_spec
#check Lorentz.rightEdgeIndex
#check Lorentz.rightEdgeIndex_spec
#check Lorentz.ghostCurveN_of_le_neg_one
#check Lorentz.ghostCurveN_of_mem_Icc_neg_one_zero
#check Lorentz.ghostCurveN_of_mem_Icc_zero_leftTime
#check Lorentz.ghostCurveN_of_mem_Icc_leftTime
#check Lorentz.ghostCurveN_one
#check Lorentz.ghostCurveN_of_mem_Icc_rightTime
#check Lorentz.ghostCurveN_of_mem_Icc_rightTime_zero_two
#check Lorentz.ghostCurveN_of_two_le
#check Lorentz.ghostCurveN_neg_one
#check Lorentz.ghostCurveN_zero
#check Lorentz.ghostCurveN_leftTime
#check Lorentz.ghostCurveN_rightTime
#check Lorentz.ghostCurveN_three_halves
#check Lorentz.ghostCurveN_two
