module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftAnchor.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.AffineInterpolation

public section

namespace Lorentz

/- Lemma 6.21b (Primal components of dangerous edges remain in D) (1): the
primal component of the left anchor edge remains in `C0Seq.remoteBall`. -/
#check (Lorentz.leftAnchorEdge_primal_mem_remoteBall :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (_ : zLeft.1.1 ∈ C0Seq.remoteBall)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall),
    Set.MapsTo
      (fun t : ℝ ↦ (AffineMap.lineMap zLeft z₀ (t + 1)).1.1)
      (Set.Icc (-1) 0) C0Seq.remoteBall)

/- Lemma 6.21b (Primal components of dangerous edges remain in D) (2): the
primal component of the affine edge from the time-zero point to the first left
dyadic vertex remains in `C0Seq.remoteBall`. -/
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

/- Lemma 6.21b (Primal components of dangerous edges remain in D) (3): the
primal component of every affine edge between consecutive left dyadic vertices
remains in `C0Seq.remoteBall`. -/
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

/- Lemma 6.21b (Primal components of dangerous edges remain in D) (4): a
primal point in `C0Seq.remoteBall` lies outside `C0Seq.localOpenUnitBall`. -/
#check (C0Seq.localOpenUnitBall_disjoint_remoteBall :
  Disjoint C0Seq.localOpenUnitBall C0Seq.remoteBall)
