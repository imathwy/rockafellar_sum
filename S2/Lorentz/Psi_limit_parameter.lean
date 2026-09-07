/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Convergence

/-!
# Limits of the Psi parameter

This module recovers scalar and sequence parameters from convergent parametrizations.
-/

public section

open Filter
open scoped Topology

namespace Lorentz

/-
Lemma 4.2b (Recovery of the scalar parameter in a convergent Ψ sequence) (1):
convergence under `Lorentz.parametrization` forces convergence of its `L1Seq` parameter.
-/
#check (Lorentz.tendstoL1Parameter :
  ∀ (d : C0Seq) (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ) (x : C0Seq) (a : L1Seq),
    Tendsto (fun k ↦ Lorentz.parametrization d (aSeq k, tSeq k)) atTop (𝓝 (x, a)) →
      Tendsto aSeq atTop (𝓝 a))

/-
Lemma 4.2b (Recovery of the scalar parameter in a convergent Ψ sequence) (2):
the scalar multiples converge to the residual `x + L1Seq.positiveOperator a`.
-/
#check (Lorentz.tendstoScalarMultiple :
  ∀ (d : C0Seq) (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ) (x : C0Seq) (a : L1Seq),
    Tendsto (fun k ↦ Lorentz.parametrization d (aSeq k, tSeq k)) atTop (𝓝 (x, a)) →
      Tendsto (fun k ↦ tSeq k • d) atTop (𝓝 (x + L1Seq.positiveOperator a)))

/-
Lemma 4.2b (Recovery of the scalar parameter in a convergent Ψ sequence) (3):
when `d ≠ 0`, there is a unique scalar limit and it recovers the first coordinate.
-/
#check (Lorentz.existsUniqueLimitParameter :
  ∀ (d : C0Seq) (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ) (x : C0Seq) (a : L1Seq),
    d ≠ 0 →
      Tendsto (fun k ↦ Lorentz.parametrization d (aSeq k, tSeq k)) atTop (𝓝 (x, a)) →
        ∃! s : ℝ, Tendsto tSeq atTop (𝓝 s) ∧
          x = -L1Seq.positiveOperator a + s • d)

end Lorentz
