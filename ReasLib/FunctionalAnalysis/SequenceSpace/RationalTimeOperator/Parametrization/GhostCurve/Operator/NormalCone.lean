/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Convex.NormalCone.Sum
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.Localization
import ReasLib.Analysis.C0Seq.NormalCone.Origin

/-!
# Ghost-curve sum with a normal cone

This module transfers local pairing bounds to the sum with the fixed
normal-cone operator and derives the polar witness.
-/

public section

open scoped Pointwise

namespace Lorentz

/-- Every point in the graph of the ghost-curve operator plus the normal cone
of `C0Seq.finalConstraint` has nonnegative quadratic pairing. -/
theorem ghostCurveSum_pairing_nonneg
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (hNZero : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (x : C0Seq) (ystar : L1Seq)
    (h_graph : (x, ystar) ∈
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
        C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph) :
    0 ≤ C0Seq.quadraticPairing (x, ystar) := by
  have hzero : (0 : C0Seq) ∈ C0Seq.finalConstraint := by
    rw [C0Seq.mem_finalConstraint]
    simp
  have hlocal : ∀ x xstar,
      (x, xstar) ∈ (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph →
        x ∈ C0Seq.localOpenUnitBall →
          0 ≤ C0Seq.coordinateDualPairing.quadratic (x, xstar) := by
    intro x xstar hx hxlocal
    have hq := quadraticPairing_nonneg_of_mem_ghostCurveOperator
      d hd h_missing zLeft z₀ hPLeft hPZero hNLeft hNZero hLeft hZero
      h h_positive h_tendsto v hvP hvN x xstar hx hxlocal
    rw [C0Seq.quadraticPairing_eq_coordinateQuadratic] at hq
    exact hq
  have hq := DualPairing.quadratic_nonneg_of_mem_graph_add_normalCone
    C0Seq.coordinateDualPairing
    (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v)
    C0Seq.finalConstraint C0Seq.localOpenUnitBall hzero
    C0Seq.finalConstraint_subset_localOpenUnitBall hlocal x ystar h_graph
  rw [C0Seq.quadraticPairing_eq_coordinateQuadratic]
  exact hq

/-- The origin belongs to the monotone polar of the graph of the ghost-curve
operator plus the normal cone of `C0Seq.finalConstraint`. -/
theorem zero_mem_monotonePolar_ghostCurveSum
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (hNZero : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16) :
    (0, 0) ∈ C0Seq.monotonePolar
      ((ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
        C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph) := by
  rw [C0Seq.mem_monotonePolar]
  intro s hs
  rcases s with ⟨x, ystar⟩
  have hq := ghostCurveSum_pairing_nonneg
    d hd h_missing zLeft z₀ hPLeft hPZero hNLeft hNZero hLeft hZero
      h h_positive h_tendsto v hvP hvN x ystar hs
  have hneg : (0, 0) - (x, ystar) = -(x, ystar) := by
    ext <;> simp
  rw [hneg, C0Seq.quadraticPairing.map_neg]
  exact hq

/-- The graph of the ghost-curve operator plus the normal cone of
`C0Seq.finalConstraint` is not maximally monotone under the ghost-curve
construction hypotheses. -/
theorem not_maximalMonotone_ghostCurveSum
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hNLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (hNZero : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (h_z₀_mem : (z₀ : C0Seq × L1Seq) ∈
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (h_z₀_neg : C0Seq.quadraticPairing z₀ < 0)
    (hM : C0Seq.coordinateDualPairing.IsMonotone
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph) :
    ¬ Maximal C0Seq.coordinateDualPairing.IsMonotone
      ((ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
        C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph) := by
  intro hmax
  have hmonoSum :=
    DualPairing.isMonotone_graph_add_normalCone
      C0Seq.coordinateDualPairing
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v)
      C0Seq.finalConstraint hM
  have hpolarSource := zero_mem_monotonePolar_ghostCurveSum
    d hd h_missing zLeft z₀ hPLeft hPZero hNLeft hNZero hLeft hZero
      h h_positive h_tendsto v hvP hvN
  have hpolar : (0, 0) ∈ C0Seq.coordinateDualPairing.monotonePolar
      ((ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
        C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph) := by
    rw [← C0Seq.monotonePolar_eq_coordinateDualPairing]
    exact hpolarSource
  have heq :=
    (C0Seq.coordinateDualPairing.maximalMonotone_iff_polar_eq _ hmonoSum).1 hmax
  have hzeroGraph : (0, 0) ∈
      ((ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
        C0Seq.coordinateDualPairing.normalCone C0Seq.finalConstraint).graph) := by
    rw [← heq]
    exact hpolar
  have hzeroNot :=
    C0Seq.zero_not_mem_add_normalCone_graph_of_quadraticPairing_neg
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v)
      (z₀ : C0Seq × L1Seq) h_z₀_mem h_z₀_neg hM
  exact hzeroNot hzeroGraph

end Lorentz
