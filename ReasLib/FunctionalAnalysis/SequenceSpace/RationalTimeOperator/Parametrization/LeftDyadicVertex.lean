module

public import ReasLib.Analysis.C0Seq.RemoteBall
public import ReasLib.Analysis.LeftDyadicTemplate
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive

public section

namespace Lorentz

/-- The prescribed error radius for the zero-based sequence of left dyadic vertices. -/
noncomputable def leftRadius (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(k + 5 : ℝ))

/-- The left dyadic vertex radius at index `k` is `2 ^ (-(k + 5))`. -/
theorem leftRadius_def (k : ℕ) :
    leftRadius k = (2 : ℝ) ^ (-(k + 5 : ℝ)) := by
  -- Unfold the named radius to expose its prescribed dyadic value.
  rfl

/-- Every left dyadic vertex radius is positive. -/
theorem leftRadius_pos (k : ℕ) :
    0 < leftRadius k := by
  -- The positive base remains positive under every real exponent.
  have hbase : (0 : ℝ) < 2 := by
    norm_num
  rw [leftRadius]
  exact Real.rpow_pos_of_pos hbase _

/-- Every left dyadic vertex radius is strictly less than one. -/
theorem leftRadius_lt_one (k : ℕ) :
    leftRadius k < 1 := by
  -- The dyadic base exceeds one, while the prescribed exponent is negative.
  have hbase : (1 : ℝ) < 2 := by
    norm_num
  have hsum : (0 : ℝ) < k + 5 := by
    positivity
  have hexponent : -(k + 5 : ℝ) < 0 := by
    exact neg_lt_zero.mpr hsum
  rw [leftRadius]
  calc
    (2 : ℝ) ^ (-(k + 5 : ℝ)) < 2 ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hbase hexponent
    _ = 1 := Real.rpow_zero 2

/-- A simultaneous choice of points in `parametrizedSubspace d` at all left dyadic times. -/
noncomputable def leftVertex (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d) : ℕ → parametrizedSubspace d :=
  fun k ↦ Classical.choose
    (exists_approx_fixedPositiveCoordinate d hd h_missing
      (leftTime k) C0Seq.farPoint
      (HilbertProd2.fst (leftTemplate (negativeCoordinate d hd z₀) (leftTime k)))
      (HilbertProd2.snd (leftTemplate (negativeCoordinate d hd z₀) (leftTime k)))
      (leftRadius k) (leftRadius_pos k))

/-- Each selected left dyadic vertex has its prescribed positive coordinate, lies over
`C0Seq.remoteBall`, and approximates the negative-coordinate template within `leftRadius k`. -/
theorem leftVertex_spec (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d) (k : ℕ) :
    positiveCoordinate d hd (leftVertex d hd h_missing z₀ k) = leftTime k ∧
      (leftVertex d hd h_missing z₀ k : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ k) -
          leftTemplate (negativeCoordinate d hd z₀) (leftTime k)‖ < leftRadius k := by
  -- Name the point selected by fixed-time simultaneous approximation.
  let z : parametrizedSubspace d := Classical.choose
    (exists_approx_fixedPositiveCoordinate d hd h_missing
      (leftTime k) C0Seq.farPoint
      (HilbertProd2.fst (leftTemplate (negativeCoordinate d hd z₀) (leftTime k)))
      (HilbertProd2.snd (leftTemplate (negativeCoordinate d hd z₀) (leftTime k)))
      (leftRadius k) (leftRadius_pos k))
  -- Record all three estimates supplied by the choice specification.
  have hs := Classical.choose_spec
    (exists_approx_fixedPositiveCoordinate d hd h_missing
      (leftTime k) C0Seq.farPoint
      (HilbertProd2.fst (leftTemplate (negativeCoordinate d hd z₀) (leftTime k)))
      (HilbertProd2.snd (leftTemplate (negativeCoordinate d hd z₀) (leftTime k)))
      (leftRadius k) (leftRadius_pos k))
  -- Align the public choice-built family with this named selected point.
  change positiveCoordinate d hd z = leftTime k ∧
      (z : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖negativeCoordinate d hd z -
          leftTemplate (negativeCoordinate d hd z₀) (leftTime k)‖ < leftRadius k
  refine ⟨hs.1, ?_, ?_⟩
  · -- Upgrade the ambient approximation using the radius bound below one.
    have hambient : dist (z : C0Seq × L1Seq).1 C0Seq.farPoint < leftRadius k := by
      simpa only [dist_eq_norm] using hs.2.1
    rw [C0Seq.mem_remoteBall]
    exact lt_trans hambient (leftRadius_lt_one k)
  · -- Reassemble the split Hilbert-product target into the original template.
    have hmk : HilbertProd2.mk
        (HilbertProd2.fst (leftTemplate (negativeCoordinate d hd z₀) (leftTime k)))
        (HilbertProd2.snd (leftTemplate (negativeCoordinate d hd z₀) (leftTime k))) =
      leftTemplate (negativeCoordinate d hd z₀) (leftTime k) := by
      exact HilbertProd2.mk_fst_snd _
    rw [← hmk]
    exact hs.2.2

/-- The positive coordinate of a selected left dyadic vertex is its left dyadic time. -/
theorem positiveCoordinate_leftVertex (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d) (k : ℕ) :
    positiveCoordinate d hd (leftVertex d hd h_missing z₀ k) = leftTime k := by
  -- Project the prescribed positive coordinate from the choice specification.
  exact (leftVertex_spec d hd h_missing z₀ k).1

/-- The first ambient coordinate of a selected left dyadic vertex lies in the remote ball. -/
theorem fst_leftVertex_mem_remoteBall (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d) (k : ℕ) :
    (leftVertex d hd h_missing z₀ k : C0Seq × L1Seq).1 ∈
      C0Seq.remoteBall := by
  -- Project remote-ball membership from the choice specification.
  exact (leftVertex_spec d hd h_missing z₀ k).2.1

/-- The negative coordinate of a selected left dyadic vertex approximates the left template. -/
theorem norm_negativeCoordinate_leftVertex_sub_leftTemplate_lt
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d) (k : ℕ) :
    ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ k) -
        leftTemplate (negativeCoordinate d hd z₀) (leftTime k)‖ < leftRadius k := by
  -- Project the negative-coordinate error estimate from the choice specification.
  exact (leftVertex_spec d hd h_missing z₀ k).2.2

end Lorentz
