/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Bounds

/-!
# Folded Detector Remainder Bounds

This module exposes uniform bounds for lower-order folded detector terms.
-/

public section

/- Lemma 6.14b (Uniform bounds for the lower-order folded terms) (1): each folded
detector perturbation has nonpositive quadratic pairing. -/
#check (Lorentz.quadraticPairing_detectorPerturbation_nonpos :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    C0Seq.quadraticPairing
      (Lorentz.detectorPerturbation d hd h_missing h h_tendsto i) ≤ 0)

/- Lemma 6.14b (Uniform bounds for the lower-order folded terms) (2): the absolute
pairing of a near-ghost base point with its detector perturbation is strictly bounded
by half the square of the scheduled radius. -/
#check (Lorentz.abs_symmetricForm_nearGhostBase_detectorPerturbation_lt :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    |C0Seq.symmetricForm (Lorentz.nearGhostBase d hd h_missing i)
      (Lorentz.detectorPerturbation d hd h_missing h h_tendsto i)| <
        DetectorTriple.rightRadius i ^ 2 / 2)

/- Lemma 6.14b (Uniform bounds for the lower-order folded terms) (3): the absolute
quadratic pairing of each near-ghost base point is at most `9 / 4`. -/
#check (Lorentz.abs_quadraticPairing_nearGhostBase_le :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (i : ℕ),
    |C0Seq.quadraticPairing (Lorentz.nearGhostBase d hd h_missing i)| ≤ (9 : ℝ) / 4)

/- Lemma 6.14b (Uniform bounds for the lower-order folded terms) (4): pairing any
ambient point with a near-ghost base point is bounded by the product of their sizes. -/
#check (Lorentz.abs_symmetricForm_nearGhostBase_le_zSize :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (w : C0Seq × L1Seq) (i : ℕ),
    |C0Seq.symmetricForm w (Lorentz.nearGhostBase d hd h_missing i)| ≤
      C0Seq.zSize w * C0Seq.zSize (Lorentz.nearGhostBase d hd h_missing i))
