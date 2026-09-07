module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Lipschitz

public section

namespace Lorentz

/- Lemma 6.12b (Adjacent folded-vertex slope estimate) (1): the
negative-coordinate displacement of adjacent folded right vertices is bounded
by their scheduled radii. -/
#check (Lorentz.norm_negativeCoordinate_rightVertex_sub_lt :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) -
        negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1))‖ <
      DetectorTriple.rightRadius i + DetectorTriple.rightRadius (i + 1))

end Lorentz

namespace DetectorTriple

/- Lemma 6.12b (Adjacent folded-vertex slope estimate) (2): adjacent scheduled
radii sum to `3 / 32` times the corresponding scheduled-time gap. -/
#check (DetectorTriple.rightRadius_add_succ : ∀ (i : ℕ),
    rightRadius i + rightRadius (i + 1) =
      (3 / 32 : ℝ) * (rightTime i - rightTime (i + 1)))

end DetectorTriple

namespace Lorentz

/- Lemma 6.12b (Adjacent folded-vertex slope estimate) (3): the
negative-coordinate displacement of adjacent folded right vertices is strictly
smaller than their scheduled-time gap. -/
#check (Lorentz.rightVertex_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    ‖negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto i) -
        negativeCoordinate d hd (rightVertex d hd h_missing h h_tendsto (i + 1))‖ <
      DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1))

end Lorentz
