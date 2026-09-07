module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.LorentzCone
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.LorentzCone
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay

public section

namespace Lorentz

/- Lemma 6.21a (Classification of the only potentially negative edges) (1):
the actual past ray lies in the past Lorentz cone and has nonnegative energy. -/
#check (Lorentz.pastRay_mem_pastCone :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (P : ℝ) (_ : P ≤ -1),
    embedding d hd (pastRay d zLeft P) ∈ pastCone (HilbertProd2 UnitL2))

#check (Lorentz.pastRay_energy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (zLeft : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (P : ℝ) (_ : P ≤ -1),
    0 ≤ energy (embedding d hd (pastRay d zLeft P)))

/- Every selected left vertex lies in the future Lorentz cone. -/
#check (Lorentz.leftVertex_mem_futureCone :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ),
    embedding d hd (leftVertex d hd h_missing z₀ k) ∈
      futureCone (HilbertProd2 UnitL2))

/- Lemma 6.21a (Classification of the only potentially negative edges) (2):
the affine edge between consecutive left vertices lies in the future Lorentz cone. -/
#check (Lorentz.leftVertexEdge_mem_futureCone :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ),
    Set.MapsTo
      (fun P : ℝ ↦
        AffineMap.lineMap
          (embedding d hd (leftVertex d hd h_missing z₀ k))
          (embedding d hd (leftVertex d hd h_missing z₀ (k + 1)))
          ((P - leftTime k) / (leftTime (k + 1) - leftTime k)))
      (Set.Icc (leftTime k) (leftTime (k + 1)))
      (futureCone (HilbertProd2 UnitL2)))

/- Lemma 6.21a (Classification of the only potentially negative edges) (3):
every point of an affine edge between consecutive left vertices has nonnegative energy. -/
#check (Lorentz.leftVertexEdge_energy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (k : ℕ) (P : ℝ) (_ : P ∈ Set.Icc (leftTime k) (leftTime (k + 1))),
    0 ≤ energy
      (AffineMap.lineMap
        (embedding d hd (leftVertex d hd h_missing z₀ k))
        (embedding d hd (leftVertex d hd h_missing z₀ (k + 1)))
        ((P - leftTime k) / (leftTime (k + 1) - leftTime k))))

/- Every folded right vertex lies in the future Lorentz cone. -/
#check (Lorentz.rightVertex_mem_futureCone :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    embedding d hd (rightVertex d hd h_missing h h_tendsto i) ∈
      futureCone (HilbertProd2 UnitL2))

/- Lemma 6.21a (Classification of the only potentially negative edges) (4):
the affine edge between consecutive folded right vertices lies in the future Lorentz cone. -/
#check (Lorentz.rightVertexEdge_mem_futureCone :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ),
    Set.MapsTo
      (fun P : ℝ ↦
        AffineMap.lineMap
          (embedding d hd (rightVertex d hd h_missing h h_tendsto (i + 1)))
          (embedding d hd (rightVertex d hd h_missing h h_tendsto i))
          ((P - DetectorTriple.rightTime (i + 1)) /
            (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1))))
      (Set.Icc (DetectorTriple.rightTime (i + 1)) (DetectorTriple.rightTime i))
      (futureCone (HilbertProd2 UnitL2)))

/- Lemma 6.21a (Classification of the only potentially negative edges) (5):
every point of an affine edge between consecutive folded right vertices has
nonnegative energy. -/
#check (Lorentz.rightVertexEdge_energy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (i : ℕ) (P : ℝ)
    (_ : P ∈ Set.Icc (DetectorTriple.rightTime (i + 1))
      (DetectorTriple.rightTime i)),
    0 ≤ energy
      (AffineMap.lineMap
        (embedding d hd (rightVertex d hd h_missing h h_tendsto (i + 1)))
        (embedding d hd (rightVertex d hd h_missing h h_tendsto i))
        ((P - DetectorTriple.rightTime (i + 1)) /
          (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1)))))

/- Lemma 6.21a (Classification of the only potentially negative edges) (6):
the bridge from the first folded right vertex to `(2 : ℝ) • v` lies in the
future Lorentz cone. -/
#check (Lorentz.foldedToFutureEdge_mem_futureCone :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    Set.MapsTo
      (fun P : ℝ ↦
        AffineMap.lineMap
          (embedding d hd (rightVertex d hd h_missing h h_tendsto 0))
          (embedding d hd ((2 : ℝ) • v))
          ((P - (3 / 2 : ℝ)) / (2 - 3 / 2)))
      (Set.Icc (3 / 2 : ℝ) 2) (futureCone (HilbertProd2 UnitL2)))

/- Lemma 6.21a (Classification of the only potentially negative edges) (7):
every point of the bridge from the first folded right vertex to `(2 : ℝ) • v`
has nonnegative energy. -/
#check (Lorentz.foldedToFutureEdge_energy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (_ : P ∈ Set.Icc (3 / 2 : ℝ) 2),
    0 ≤ energy
      (AffineMap.lineMap
        (embedding d hd (rightVertex d hd h_missing h h_tendsto 0))
        (embedding d hd ((2 : ℝ) • v))
        ((P - (3 / 2 : ℝ)) / (2 - 3 / 2))))

/- Lemma 6.21a (Classification of the only potentially negative edges) (8):
the actual future ray lies in the future Lorentz cone and has nonnegative energy. -/
#check (Lorentz.futureRay_mem_futureCone :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (_ : 2 ≤ P),
    embedding d hd (P • v) ∈ futureCone (HilbertProd2 UnitL2))

#check (Lorentz.futureRay_energy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (_ : 2 ≤ P),
    0 ≤ energy (embedding d hd (P • v)))

end Lorentz
