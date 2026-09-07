/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Pointwise

/-!
# Pointwise representatives of interval-coordinate sums

This module exposes a pointwise scalar-series representative of the
interval-coordinate synthesis map and its almost-everywhere specification.
-/

noncomputable section

/- The shared pointwise representative and its computation rule. -/
#check (L1Seq.pointwiseRepresentative : L1Seq → ℝ → ℝ)

/- The defining scalar series of the shared representative. -/
#check (L1Seq.pointwiseRepresentative_apply :
  ∀ (a : L1Seq) (s : ℝ),
    L1Seq.pointwiseRepresentative a s =
      ∑' n : ℕ,
        a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) s)

/- Lemma 2.7a (Pointwise absolutely convergent representative of Va) (1):
the scalar indicator series is absolutely summable at every real point. -/
#check (L1Seq.summable_abs_pointwiseRepresentative :
  ∀ (a : L1Seq) (s : ℝ),
    Summable (fun n : ℕ ↦
      |a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) s|))

/- Lemma 2.7a (Pointwise absolutely convergent representative of Va) (2):
the scalar series represents `L1Seq.intervalCoordinateOperator a` almost everywhere. -/
#check (L1Seq.pointwiseRepresentative_ae_eq :
  ∀ a : L1Seq,
    (fun s : ℝ ↦ L1Seq.pointwiseRepresentative a s) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun s : ℝ ↦ L1Seq.intervalCoordinateOperator a s))

/- Lemma 2.7a (Pointwise absolutely convergent representative of Va) (3):
if `L1Seq.intervalCoordinateOperator a` is zero, its scalar representative vanishes
on a conull subset of the open unit interval. -/
#check (L1Seq.pointwiseRepresentative_exists_conull_zero :
  ∀ a : L1Seq, L1Seq.intervalCoordinateOperator a = 0 →
    ∃ E : Set ℝ,
      E ⊆ Set.Ioo (0 : ℝ) 1 ∧
        MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 \ E) = 0 ∧
          ∀ s ∈ E, L1Seq.pointwiseRepresentative a s = 0)
