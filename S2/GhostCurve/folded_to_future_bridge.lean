module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.AffineInterpolation

public section

namespace Lorentz

/- Lemma 6.17a (Bridge from the outer folded vertex to 2v) (1): the
negative-coordinate gap from the first folded right vertex to `(2 : ℝ) • v` is
strictly less than `1 / 2`. -/
#check (Lorentz.foldedToFuture_gap_lt_half :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0) -
        negativeCoordinate d hd ((2 : ℝ) • v)‖ < (1 : ℝ) / 2)

/- Lemma 6.17a (Bridge from the outer folded vertex to 2v) (2): the affine
negative-coordinate edge from the first folded right vertex at `3 / 2` to
`(2 : ℝ) • v` at `2` has a Lipschitz constant strictly less than `1`. -/
#check (Lorentz.foldedToFutureEdge_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    ∃ K : NNReal, K < 1 ∧
      LipschitzOnWith K
        (fun P : ℝ ↦
          AffineMap.lineMap
            (negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto 0))
            (negativeCoordinate d hd ((2 : ℝ) • v))
            ((P - (3 / 2 : ℝ)) / (2 - 3 / 2)))
        (Set.Icc (3 / 2 : ℝ) 2))

end Lorentz
