module

public import ReasLib.Analysis.AffineInterpolation
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex

public section

namespace Lorentz

/-- The primal component of the affine edge from a time-zero point in
`C0Seq.remoteBall` to the first left dyadic vertex stays in `C0Seq.remoteBall`. -/
theorem initialLeftVertexEdge_primal_mem_remoteBall
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd z₀ = 0)
    (hZero : z₀.1.1 ∈ C0Seq.remoteBall) :
    Set.MapsTo
      (fun P : ℝ ↦
        (AffineMap.lineMap z₀ (leftVertex d hd h_missing z₀ 0)
          ((P - 0) / (leftTime 0 - 0))).1.1)
      (Set.Icc 0 (leftTime 0)) C0Seq.remoteBall := by
  have htime : (0 : ℝ) < leftTime 0 := by
    rw [leftTime_def]
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hleft := fst_leftVertex_mem_remoteBall d hd h_missing z₀ 0
  have hmaps := Convex.mapsTo_lineMap_interval
    (a := (0 : ℝ)) (b := leftTime 0)
    (u := z₀.1.1) (v := (leftVertex d hd h_missing z₀ 0 : C0Seq × L1Seq).1)
    (C := C0Seq.remoteBall) htime C0Seq.convex_remoteBall hZero hleft
  intro P hP
  have hmapsP := hmaps hP
  simpa only [AffineMap.lineMap_apply_module, Submodule.coe_add, Submodule.coe_smul,
    Prod.fst_add, Prod.smul_fst, sub_zero, div_one, zero_add] using hmapsP

/-- The primal component of every affine edge between consecutive left dyadic
vertices stays in `C0Seq.remoteBall`. -/
theorem leftVertexEdge_primal_mem_remoteBall
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d) (k : ℕ) :
    Set.MapsTo
      (fun P : ℝ ↦
        (AffineMap.lineMap (leftVertex d hd h_missing z₀ k)
          (leftVertex d hd h_missing z₀ (k + 1))
          ((P - leftTime k) / (leftTime (k + 1) - leftTime k))).1.1)
      (Set.Icc (leftTime k) (leftTime (k + 1))) C0Seq.remoteBall := by
  have hgap : 0 < leftTime (k + 1) - leftTime k := by
    rw [leftTime_succ_sub]
    positivity
  have hleft := fst_leftVertex_mem_remoteBall d hd h_missing z₀ k
  have hright := fst_leftVertex_mem_remoteBall d hd h_missing z₀ (k + 1)
  have hmaps := Convex.mapsTo_lineMap_interval
    (a := leftTime k) (b := leftTime (k + 1))
    (u := (leftVertex d hd h_missing z₀ k : C0Seq × L1Seq).1)
    (v := (leftVertex d hd h_missing z₀ (k + 1) : C0Seq × L1Seq).1)
    (C := C0Seq.remoteBall) (sub_pos.mp hgap) C0Seq.convex_remoteBall hleft hright
  intro P hP
  have hmapsP := hmaps hP
  simpa only [AffineMap.lineMap_apply_module, Submodule.coe_add, Submodule.coe_smul,
    Prod.fst_add, Prod.smul_fst] using hmapsP

end Lorentz
