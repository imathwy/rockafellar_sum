module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftAnchor.AffineInterpolation

public section

namespace Lorentz

/- Lemma 6.3 (A left anchor and a strict bridge to time zero) (1):
the quantitative left-anchor choice. -/
#check (Lorentz.exists_leftAnchor :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (_ : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ) →
    ∃ zLeft : Lorentz.parametrizedSubspace d,
      Lorentz.positiveCoordinate d hd zLeft = -1 ∧
      (zLeft : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖Lorentz.negativeCoordinate d hd zLeft -
          (2 : ℝ) • Lorentz.negativeCoordinate d hd z₀‖ < (1 / 64 : ℝ) ∧
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 / 16 : ℝ) ∧
      ‖Lorentz.negativeCoordinate d hd zLeft -
          Lorentz.negativeCoordinate d hd z₀‖ < 1)

/- Lemma 6.3 (A left anchor and a strict bridge to time zero) (2): the
negative-coordinate component of the affine edge from `zLeft` at time `-1` to
`z₀` at time `0` has a Lipschitz constant strictly less than `1`. -/
#check (Lorentz.leftAnchorEdge_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd zLeft = -1)
    (_ : Lorentz.positiveCoordinate d hd z₀ = 0),
    ‖Lorentz.negativeCoordinate d hd zLeft -
        Lorentz.negativeCoordinate d hd z₀‖ < 1 →
    ∃ K : NNReal, K < 1 ∧
      LipschitzOnWith K
        (fun t : ℝ ↦
          (AffineMap.lineMap (Lorentz.embedding d hd zLeft)
            (Lorentz.embedding d hd z₀) (t + 1)).2)
        (Set.Icc (-1) 0))

/- Lemma 6.3 (A left anchor and a strict bridge to time zero) (3): the primal
component of the affine edge from `zLeft` at time `-1` to `z₀` at time `0`
remains in `C0Seq.remoteBall`. -/
#check (Lorentz.leftAnchorEdge_primal_mem_remoteBall :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd zLeft = -1)
    (_ : Lorentz.positiveCoordinate d hd z₀ = 0)
    (_ : zLeft.1.1 ∈ C0Seq.remoteBall)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall),
    Set.MapsTo
      (fun t : ℝ ↦ (AffineMap.lineMap zLeft z₀ (t + 1)).1.1)
      (Set.Icc (-1) 0) C0Seq.remoteBall)

end Lorentz
