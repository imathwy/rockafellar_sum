/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates

/-!
# Folded Vertex Coordinates

This module exposes positive-coordinate and norm bounds for folded vertices.
-/

public section

namespace Lorentz

/- Lemma 6.12a (Coordinates and N-bound of folded vertices) (1): each folded
detector perturbation has zero positive coordinate. -/
#check (Lorentz.positiveCoordinate_detectorPerturbation :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    positiveCoordinate d hd
      (detectorPerturbation d hd h_missing h h_tendsto i) = 0)

/- Lemma 6.12a (Coordinates and N-bound of folded vertices) (2): the positive
coordinate of each folded right vertex is its scheduled right time. -/
#check (Lorentz.positiveCoordinate_rightVertex :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    positiveCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) =
      DetectorTriple.rightTime i)

/- Lemma 6.12a (Coordinates and N-bound of folded vertices) (3): the norm of
the negative coordinate of each folded right vertex is below its scheduled radius. -/
#check (Lorentz.norm_negativeCoordinate_rightVertex_lt :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i)‖ <
      DetectorTriple.rightRadius i)

end Lorentz
