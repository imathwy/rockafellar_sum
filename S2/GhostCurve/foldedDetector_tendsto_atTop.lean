/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Asymptotics

/-!
# Folded Detector Asymptotics

This module exposes cofinal pairing gaps for folded right vertices.
-/

public section

/- Lemma 6.15a (Detector dominance over all remainder terms): for every exterior
point and every real threshold, some arbitrarily late folded right vertex has
pairing gap above that threshold. -/
#check (Lorentz.rightVertex_sub_quadraticPairing_cofinal :
  ∀
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (w : C0Seq × L1Seq) (_ : w ∉ Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (_ : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (Lorentz.detectorFunctional d p q w))),
    ∀ (R : ℝ) (N : ℕ), ∃ i : ℕ, N ≤ i ∧
      R < C0Seq.symmetricForm w
          (Lorentz.rightVertex d hd h_missing h h_tendsto i) -
        C0Seq.quadraticPairing
          (Lorentz.rightVertex d hd h_missing h h_tendsto i))
