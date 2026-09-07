/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Realization
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SamePositiveCoordinate

/-!
# Rigidity in the monotone polar of the ghost curve

This module shows that monotone-polar points away from ghost time have the
prescribed negative coordinate and therefore lie on the operator graph.
-/

public section

namespace Lorentz

/-- A point in the monotone polar of `ghostGraph`, away from ghost time, has
negative coordinate prescribed by `ghostCurveN`. -/
theorem negativeCoordinate_eq_ghostCurveN_of_mem_polar
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (hvP : positiveCoordinate d hd v = 1)
    (w : parametrizedSubspace d)
    (h_polar : w.val ∈ C0Seq.monotonePolar
      (ghostGraph d hd h_missing zLeft z₀ h h_tendsto v))
    (hP_ne : positiveCoordinate d hd w ≠ 1) :
    negativeCoordinate d hd w =
      ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
        (positiveCoordinate d hd w) := by
  obtain ⟨m, hm⟩ :=
    (existsUnique_ghostCurveN_preimage d hd h_missing zLeft z₀ hPLeft hPZero h
      h_positive h_tendsto v hvP (positiveCoordinate d hd w) hP_ne).exists
  have hm_graph : m.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
    apply (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v m).2
    have hmP_ne : positiveCoordinate d hd m ≠ 1 := by
      simpa only [hm.1] using hP_ne
    have hmN : negativeCoordinate d hd m =
        ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
          (positiveCoordinate d hd m) := by
      rw [hm.1]
      exact hm.2
    exact ⟨hmP_ne, hmN⟩
  have hquad : 0 ≤ C0Seq.quadraticPairing (w.val - m.val) := by
    exact (C0Seq.mem_monotonePolar _ w.val).1 h_polar m.val hm_graph
  have hquad_sub : 0 ≤ C0Seq.quadraticPairing (w - m) := by
    exact hquad
  have hsame : positiveCoordinate d hd w = positiveCoordinate d hd m := by
    exact hm.1.symm
  have hrigid := sameP_rigidity d hd w m hsame hquad_sub
  exact hrigid.trans hm.2

/-- A point in the monotone polar of the ghost-curve operator graph, away from
ghost time, belongs to that graph. -/
theorem mem_ghostCurveOperator_of_polar_ne_one
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (hvP : positiveCoordinate d hd v = 1)
    (w : parametrizedSubspace d)
    (h_polar : w.val ∈ C0Seq.monotonePolar
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (hP_ne : positiveCoordinate d hd w ≠ 1) :
    w.val ∈ (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph := by
  have h_polar_ghost : w.val ∈ C0Seq.monotonePolar
      (ghostGraph d hd h_missing zLeft z₀ h h_tendsto v) := by
    rw [← graph_ghostCurveOperator]
    exact h_polar
  have hN := negativeCoordinate_eq_ghostCurveN_of_mem_polar
    d hd h_missing zLeft z₀ h h_tendsto v hPLeft hPZero h_positive hvP
      w h_polar_ghost hP_ne
  have hw_ghost : w.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
    apply (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v w).2
    exact ⟨hP_ne, hN⟩
  rw [graph_ghostCurveOperator]
  exact hw_ghost

end Lorentz
