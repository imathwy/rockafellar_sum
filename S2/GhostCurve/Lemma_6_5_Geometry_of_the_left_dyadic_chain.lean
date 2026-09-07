module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Asymptotics
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.AffineInterpolation

public section

namespace Lorentz

/- Lemma 6.5 (Geometry of the left dyadic chain) (1): consecutive selected
left vertices have negative-coordinate displacement strictly below their time gap. -/
#check (Lorentz.leftVertex_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ),
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ (k + 1)) -
        negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ <
      leftTime (k + 1) - leftTime k)

/- Lemma 6.5 (Geometry of the left dyadic chain) (2): the initial edge from
the time-zero point to the first selected left vertex has slope strictly less than `1`. -/
#check (Lorentz.initialLeftVertex_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd z₀ = 0)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)),
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ 0) -
        negativeCoordinate d hd z₀‖ < leftTime 0)

/- Lemma 6.5 (Geometry of the left dyadic chain) (3): the negative coordinates
of the selected left vertices converge to the ghost coordinate `0`. -/
#check (Lorentz.leftVertex_tendsto_ghost :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)),
    Filter.Tendsto
      (fun k ↦ negativeCoordinate d hd (leftVertex d hd h_missing z₀ k))
      Filter.atTop (nhds 0))

/- Lemma 6.5 (Geometry of the left dyadic chain) (4): every selected left
vertex satisfies the strict cone bound before ghost time `1`. -/
#check (Lorentz.leftVertex_norm_lt :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)),
    ∀ k, ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ <
      1 - leftTime k)

/- Lemma 6.5 (Geometry of the left dyadic chain) (5): every primal point of
the affine edge from the time-zero point to the first left vertex remains in
`C0Seq.remoteBall`. -/
#check (Lorentz.initialLeftVertexEdge_primal_mem_remoteBall :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd z₀ = 0)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall),
    Set.MapsTo
      (fun P : ℝ ↦
        (AffineMap.lineMap z₀ (leftVertex d hd h_missing z₀ 0)
          ((P - 0) / (leftTime 0 - 0))).1.1)
      (Set.Icc 0 (leftTime 0)) C0Seq.remoteBall)

/- Lemma 6.5 (Geometry of the left dyadic chain) (6): every primal point of
each affine edge between consecutive selected left vertices remains in
`C0Seq.remoteBall`. -/
#check (Lorentz.leftVertexEdge_primal_mem_remoteBall :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d) (k : ℕ),
    Set.MapsTo
      (fun P : ℝ ↦
        (AffineMap.lineMap (leftVertex d hd h_missing z₀ k)
          (leftVertex d hd h_missing z₀ (k + 1))
          ((P - leftTime k) / (leftTime (k + 1) - leftTime k))).1.1)
      (Set.Icc (leftTime k) (leftTime (k + 1))) C0Seq.remoteBall)

end Lorentz
