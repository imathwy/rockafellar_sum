module

public import ReasLib.Analysis.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftAnchor
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding

public section

namespace Lorentz

/-- The negative-coordinate projection of the embedded affine line from a
negative-one point to a time-zero point has a Lipschitz constant strictly below
one when the endpoint negative coordinates are less than one apart. -/
theorem leftAnchorEdge_slope_lt_one (d : C0Seq) (hd : d ≠ 0)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (hN : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1) :
    ∃ K : NNReal, K < 1 ∧
      LipschitzOnWith K
        (fun t : ℝ ↦
          (AffineMap.lineMap (embedding d hd zLeft) (embedding d hd z₀) (t + 1)).2)
        (Set.Icc (-1) 0) := by
  -- Use the distance between the negative-coordinate endpoints as the slope budget.
  let K : NNReal := Real.toNNReal
    ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖
  have hK : K < 1 := by
    exact Real.toNNReal_lt_one.mpr hN
  have hEndpoint :
      ‖negativeCoordinate d hd z₀ - negativeCoordinate d hd zLeft‖ ≤
        (K : ℝ) * (0 - (-1)) := by
    dsimp only [K]
    rw [norm_sub_rev, Real.coe_toNNReal _ (norm_nonneg _)]
    norm_num
  -- The canonical interval estimate applies after normalizing `[-1, 0]` to `[0, 1]`.
  have hLipschitz := AffineMap.lipschitzOnWith_lineMap_interval
    (a := (-1 : ℝ)) (b := 0)
    (u := negativeCoordinate d hd zLeft)
    (v := negativeCoordinate d hd z₀) (K := K) (by norm_num) hEndpoint
  refine ⟨K, hK, ?_⟩
  -- Projection from the Lorentz embedding commutes with affine interpolation.
  simpa only [AffineMap.snd_lineMap, embedding_apply, sub_neg_eq_add,
    zero_add, div_one] using hLipschitz

/-- The primal projection of the affine line from a negative-one point to a
time-zero point stays in `C0Seq.remoteBall` when both endpoints lie there. -/
theorem leftAnchorEdge_primal_mem_remoteBall (d : C0Seq) (hd : d ≠ 0)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (hLeft : zLeft.1.1 ∈ C0Seq.remoteBall)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall) :
    Set.MapsTo
      (fun t : ℝ ↦ (AffineMap.lineMap zLeft z₀ (t + 1)).1.1)
      (Set.Icc (-1) 0) C0Seq.remoteBall := by
  -- Convexity keeps the normalized affine segment between the primal endpoints in the ball.
  have hMaps := Convex.mapsTo_lineMap_interval
    (a := (-1 : ℝ)) (b := 0) (u := zLeft.1.1) (v := z₀.1.1)
    (C := C0Seq.remoteBall) (by norm_num) C0Seq.convex_remoteBall hLeft hZero
  -- Taking the primal projection commutes with the subspace-valued line map.
  simpa only [AffineMap.lineMap_apply_module, Submodule.coe_add,
    Submodule.coe_smul, Prod.fst_add, Prod.smul_fst, sub_neg_eq_add,
    zero_add, div_one] using hMaps

end Lorentz
