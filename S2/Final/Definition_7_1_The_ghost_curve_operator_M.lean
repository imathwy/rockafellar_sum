/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator

/-!
# The Ghost-Curve Operator

This module records the source-facing definition and graph of `M`.
-/

/- Definition 7.1 (The ghost-curve operator $M$): its graph is the ambient
preimage of the restricted ghost curve at the real parameters `P ≠ 1`. -/
#check (Lorentz.ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (zLeft z₀ : Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (v : Lorentz.parametrizedSubspace d),
    SetValuedOperator C0Seq L1Seq)

#check (Lorentz.graph_ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (zLeft z₀ : Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (v : Lorentz.parametrizedSubspace d),
    (Lorentz.ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph =
      Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v)

#check (Lorentz.ghostGraph_eq_preimage_graphOn :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (zLeft z₀ : Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (v : Lorentz.parametrizedSubspace d),
    Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v =
      Subtype.val '' ((Lorentz.embedding d hd) ⁻¹'
        Set.graphOn
          (Lorentz.ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
          {P : ℝ | P ≠ 1}))
