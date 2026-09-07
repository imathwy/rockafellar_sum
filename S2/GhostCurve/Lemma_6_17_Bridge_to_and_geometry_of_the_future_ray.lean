module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay

/- The endpoint gap estimate underlying the affine bridge. -/
#check (Lorentz.foldedToFuture_gap_lt_half :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    ‖Lorentz.negativeCoordinate d hd
          (Lorentz.rightVertex d hd h_missing h h_tendsto 0) -
        Lorentz.negativeCoordinate d hd ((2 : ℝ) • v)‖ < (1 : ℝ) / 2)

/- Lemma 6.17 (Bridge to and geometry of the future ray) (1): the first folded
right vertex connects to `(2 : ℝ) • v` by an affine negative-coordinate edge
of slope strictly less than `1`. -/
#check (Lorentz.foldedToFutureEdge_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    ∃ K : NNReal, K < 1 ∧
      LipschitzOnWith K
        (fun P : ℝ ↦
          AffineMap.lineMap
            (Lorentz.negativeCoordinate d hd
              (Lorentz.rightVertex d hd h_missing h h_tendsto 0))
            (Lorentz.negativeCoordinate d hd ((2 : ℝ) • v))
            ((P - (3 / 2 : ℝ)) / (2 - 3 / 2)))
        (Set.Icc (3 / 2 : ℝ) 2))

/- Lemma 6.17 (Bridge to and geometry of the future ray) (2): `P • v` is an
actual point of the Lorentz embedding. -/
#check (Lorentz.futureRay_mem_embeddingRange :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd v = 1) (P : ℝ) (_ : 2 ≤ P),
    (P, Lorentz.negativeCoordinate d hd (P • v)) ∈ Lorentz.embeddingRange d hd)

/- Lemma 6.17 (Bridge to and geometry of the future ray) (3): the future ray
has slope `‖N(v)‖ < 1`. -/
#check (Lorentz.futureRay_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 →
      ‖Lorentz.negativeCoordinate d hd v‖ < 1)

/- Lemma 6.17 (Bridge to and geometry of the future ray) (4): for `2 ≤ P`, the
future ray satisfies `‖N(P • v)‖ < P / 16 ≤ P - 1`. -/
#check (Lorentz.futureRay_negativeCoordinate_bounds :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 →
      ∀ (P : ℝ), 2 ≤ P →
        ‖Lorentz.negativeCoordinate d hd (P • v)‖ < P / 16 ∧ P / 16 ≤ P - 1)
