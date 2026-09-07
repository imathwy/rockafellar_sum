/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import S2.Lorentz.Psi_injective
public import S2.Lorentz.Psi_limit_parameter
public import S2.Lorentz.isClosed_C
public import S2.PositiveOperator.Definition_3_9_A_missing_range_vector_and_its_coordinate_functional

/-!
# Parametrization uniqueness and closedness

This module records injectivity and convergence facts for the fixed parametrized subspace.
-/

open scoped Topology

/- Lemma 4.2 (Unique parametrization and closedness of $C$) (1): the parametrization
at the fixed normalized vector outside the range of `L1Seq.positiveOperator` is injective. -/
#check (Lorentz.parametrization_injective
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
    (norm_ne_zero_iff.mp
      ((ContinuousLinearMap.unitVectorOutsideRange_spec
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective).2.symm ▸ one_ne_zero)) :
  Function.Injective
    (Lorentz.parametrization
      (ContinuousLinearMap.unitVectorOutsideRange
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)))

/- Lemma 4.2 (Unique parametrization and closedness of $C$) (2): convergence under the
fixed parametrization recovers convergence of the `L1Seq` parameter. -/
#check (Lorentz.tendstoL1Parameter
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ) (x : C0Seq) (a : L1Seq),
    Filter.Tendsto
        (fun k ↦ Lorentz.parametrization
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
          (aSeq k, tSeq k)) Filter.atTop (𝓝 (x, a)) →
      Filter.Tendsto aSeq Filter.atTop (𝓝 a))

/- Lemma 4.2 (Unique parametrization and closedness of $C$) (3): the scalar multiples
of the fixed direction converge to `x + L1Seq.positiveOperator a`. -/
#check (Lorentz.tendstoScalarMultiple
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  ∀ (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ) (x : C0Seq) (a : L1Seq),
    Filter.Tendsto
        (fun k ↦ Lorentz.parametrization
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
          (aSeq k, tSeq k)) Filter.atTop (𝓝 (x, a)) →
      Filter.Tendsto
        (fun k ↦ tSeq k • ContinuousLinearMap.unitVectorOutsideRange
          L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
        Filter.atTop (𝓝 (x + L1Seq.positiveOperator a)))

/- Lemma 4.2 (Unique parametrization and closedness of $C$) (4): convergence under the
fixed parametrization determines a unique limiting scalar and reconstructs `x`. -/
#check (Lorentz.existsUniqueLimitParameter
    (d := ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
    (hd := norm_ne_zero_iff.mp
      ((ContinuousLinearMap.unitVectorOutsideRange_spec
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective).2.symm ▸ one_ne_zero)) :
  ∀ (aSeq : ℕ → L1Seq) (tSeq : ℕ → ℝ) (x : C0Seq) (a : L1Seq),
    Filter.Tendsto
        (fun k ↦ Lorentz.parametrization
          (ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
          (aSeq k, tSeq k)) Filter.atTop (𝓝 (x, a)) →
      ∃! s : ℝ, Filter.Tendsto tSeq Filter.atTop (𝓝 s) ∧
        x = -L1Seq.positiveOperator a +
          s • ContinuousLinearMap.unitVectorOutsideRange
            L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)

/- Lemma 4.2 (Unique parametrization and closedness of $C$) (5): the source subspace
`C` is the bundled range of the parametrization at the fixed direction. -/
#check (Lorentz.parametrizedSubspace
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
  Submodule ℝ (C0Seq × L1Seq))

/- Lemma 4.2 (Unique parametrization and closedness of $C$) (6): the parametrized
subspace at the fixed direction is closed. -/
#check (Lorentz.isClosed_parametrizedSubspace
    (ContinuousLinearMap.unitVectorOutsideRange
      L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective)
    (norm_ne_zero_iff.mp
      ((ContinuousLinearMap.unitVectorOutsideRange_spec
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective).2.symm ▸ one_ne_zero)) :
  IsClosed
    (Lorentz.parametrizedSubspace
      (ContinuousLinearMap.unitVectorOutsideRange
        L1Seq.positiveOperator L1Seq.positiveOperator_not_surjective) :
      Set (C0Seq × L1Seq)))
