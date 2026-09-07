/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization
public import ReasLib.Topology.Maps.ClosedEmbedding
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Convergence of parametrized points

This module extracts parameter convergence and uniqueness from convergent
parametrized sequences.
-/

public section

open Filter
open scoped Topology

namespace Lorentz

/-- Convergence under `parametrization` forces convergence of its `L1Seq` parameter. -/
theorem tendstoL1Parameter (d : C0Seq) (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ)
    (x : C0Seq) (a : L1Seq)
    (hΨ : Tendsto (fun k ↦ parametrization d (aSeq k, tSeq k)) atTop (𝓝 (x, a))) :
    Tendsto aSeq atTop (𝓝 a) := by
  -- Project the product limit to its second coordinate.
  have hSecond := (continuous_snd.tendsto (x, a)).comp hΨ
  -- The public evaluation rule identifies that coordinate with `aSeq`.
  have hSecondCoordinate :
      (Prod.snd ∘ fun k ↦ parametrization d (aSeq k, tSeq k)) =ᶠ[atTop] aSeq := by
    apply Eventually.of_forall
    intro k
    dsimp only [Function.comp_apply]
    rw [parametrization_apply]
  exact hSecond.congr' hSecondCoordinate

/-- The scalar multiples in a convergent parametrized sequence converge to the residual
`x + L1Seq.positiveOperator a`. -/
theorem tendstoScalarMultiple (d : C0Seq) (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ)
    (x : C0Seq) (a : L1Seq)
    (hΨ : Tendsto (fun k ↦ parametrization d (aSeq k, tSeq k)) atTop (𝓝 (x, a))) :
    Tendsto (fun k ↦ tSeq k • d) atTop (𝓝 (x + L1Seq.positiveOperator a)) := by
  -- Project the original convergence to the first coordinate.
  have hFirst : Tendsto
      (fun k ↦ (parametrization d (aSeq k, tSeq k)).1) atTop (𝓝 x) :=
    (continuous_fst.tendsto (x, a)).comp hΨ
  -- Continuity of the positive operator transports the second-coordinate limit.
  have hOperator : Tendsto (fun k ↦ L1Seq.positiveOperator (aSeq k)) atTop
      (𝓝 (L1Seq.positiveOperator a)) :=
    (L1Seq.positiveOperator.continuous.tendsto a).comp
      (tendstoL1Parameter d aSeq tSeq x a hΨ)
  have hSum : Tendsto
      (fun k ↦ (parametrization d (aSeq k, tSeq k)).1 +
        L1Seq.positiveOperator (aSeq k)) atTop
      (𝓝 (x + L1Seq.positiveOperator a)) := hFirst.add hOperator
  -- Adding the operator term cancels the negative term in the parametrization.
  have hCancel : (fun k ↦ (parametrization d (aSeq k, tSeq k)).1 +
      L1Seq.positiveOperator (aSeq k)) =ᶠ[atTop] (fun k ↦ tSeq k • d) := by
    apply Eventually.of_forall
    intro k
    dsimp only
    rw [parametrization_apply]
    dsimp only [Prod.fst]
    abel
  exact hSum.congr' hCancel

/-- For a nonzero direction, a convergent parametrized sequence has a unique scalar limit,
which reconstructs its first limiting coordinate. -/
theorem existsUniqueLimitParameter (d : C0Seq) (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ)
    (x : C0Seq) (a : L1Seq) (hd : d ≠ 0)
    (hΨ : Tendsto (fun k ↦ parametrization d (aSeq k, tSeq k)) atTop (𝓝 (x, a))) :
    ∃! s : ℝ, Tendsto tSeq atTop (𝓝 s) ∧
      x = -L1Seq.positiveOperator a + s • d := by
  -- Closed-embedding recovery reflects the residual convergence to a unique scalar limit.
  have hMapped : Tendsto ((fun s : ℝ ↦ s • d) ∘ tSeq) atTop
      (𝓝 (x + L1Seq.positiveOperator a)) := by
    have hScalarMultiple := tendstoScalarMultiple d aSeq tSeq x a hΨ
    have hComposition : (fun k ↦ tSeq k • d) =ᶠ[atTop]
        ((fun s : ℝ ↦ s • d) ∘ tSeq) := by
      apply Eventually.of_forall
      intro k
      rfl
    exact hScalarMultiple.congr' hComposition
  have hRecovered : ∃! s : ℝ, Tendsto tSeq atTop (𝓝 s) ∧
      x + L1Seq.positiveOperator a = s • d :=
    (isClosedEmbedding_smul_left hd).existsUnique_tendsto tSeq atTop
      (x + L1Seq.positiveOperator a) hMapped
  rcases hRecovered with ⟨s, ⟨hs, hResidual⟩, hUnique⟩
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  -- Rearrange the residual identity into the requested reconstruction formula.
  · calc
      x = (x + L1Seq.positiveOperator a) - L1Seq.positiveOperator a := by abel
      _ = s • d - L1Seq.positiveOperator a := by rw [hResidual]
      _ = -L1Seq.positiveOperator a + s • d := by abel
  -- Any competing reconstruction yields the same residual equation and hence the same scalar.
  · intro s' hs'
    apply hUnique s'
    refine ⟨hs'.1, ?_⟩
    calc
      x + L1Seq.positiveOperator a =
          (-L1Seq.positiveOperator a + s' • d) + L1Seq.positiveOperator a := by
            rw [hs'.2]
      _ = s' • d := by abel

end Lorentz
