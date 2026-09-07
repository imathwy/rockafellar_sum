module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

public section

namespace C0Seq

/-- The symmetric cross-pairing on the primal-dual product, bundled as a continuous
bilinear map. -/
noncomputable def prodPairingL :
    (C0Seq × L1Seq) →L[ℝ] (C0Seq × L1Seq) →L[ℝ] ℝ :=
  pairingL.bilinearComp
      (ContinuousLinearMap.fst ℝ C0Seq L1Seq) (ContinuousLinearMap.snd ℝ C0Seq L1Seq) +
    pairingL.flip.bilinearComp
      (ContinuousLinearMap.snd ℝ C0Seq L1Seq) (ContinuousLinearMap.fst ℝ C0Seq L1Seq)

/-- The bundled cross-pairing evaluates as the sum of the two coordinate pairings. -/
@[simp]
theorem prodPairingL_apply (z w : C0Seq × L1Seq) :
    prodPairingL z w = pairingL z.1 w.2 + pairingL w.1 z.2 := by
  -- Evaluate the two bundled bilinear summands on their respective coordinates.
  simp [prodPairingL, ContinuousLinearMap.bilinearComp_apply]

/-- The coordinate-sum size of a primal-dual point. -/
noncomputable def zSize (z : C0Seq × L1Seq) : ℝ :=
  ‖z.1‖ + ‖z.2‖

/-- The size of an explicit primal-dual pair is the sum of its two norms. -/
@[simp]
theorem zSize_apply (x : C0Seq) (a : L1Seq) :
    zSize (x, a) = ‖x‖ + ‖a‖ := by
  -- Both projections of an explicit pair reduce definitionally.
  rfl

/-- The coordinate-sum size is the canonical `WithLp 1` product norm. -/
theorem zSize_eq_norm_toLp (z : C0Seq × L1Seq) :
    zSize z = ‖WithLp.toLp 1 z‖ := by
  -- Record the positivity required by the exponent-one product-norm formula.
  have hOne : (0 : ℝ) < (1 : ENNReal).toReal := by
    norm_num
  -- Expand the source size and identify it with the canonical product norm.
  change ‖z.1‖ + ‖z.2‖ = ‖WithLp.toLp 1 z‖
  rw [WithLp.prod_norm_eq_add hOne]
  simp

/-- The coordinate-sum size is subadditive. -/
theorem zSize_add_le (z w : C0Seq × L1Seq) :
    zSize (z + w) ≤ zSize z + zSize w := by
  -- Expose the coordinate norms so each coordinate triangle inequality applies.
  change ‖z.1 + w.1‖ + ‖z.2 + w.2‖ ≤
    (‖z.1‖ + ‖z.2‖) + (‖w.1‖ + ‖w.2‖)
  calc
    ‖z.1 + w.1‖ + ‖z.2 + w.2‖ ≤
        (‖z.1‖ + ‖w.1‖) + (‖z.2‖ + ‖w.2‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ = (‖z.1‖ + ‖z.2‖) + (‖w.1‖ + ‖w.2‖) := by ring

/-- The coordinate-sum size is absolutely homogeneous under real scalar multiplication. -/
theorem zSize_smul (c : ℝ) (z : C0Seq × L1Seq) :
    zSize (c • z) = |c| * zSize z := by
  -- Pull the scalar norm from both coordinate norms and regroup the result.
  change ‖c • z.1‖ + ‖c • z.2‖ = |c| * (‖z.1‖ + ‖z.2‖)
  simp only [norm_smul, Real.norm_eq_abs]
  ring

/-- The symmetric cross-pairing is bounded by the product of the coordinate-sum sizes. -/
theorem abs_prodPairingL_le (z w : C0Seq × L1Seq) :
    |prodPairingL z w| ≤ zSize z * zSize w := by
  -- Expand the symmetric pairing into its two cross-coordinate pairings.
  rw [prodPairingL_apply]
  calc
    |pairingL z.1 w.2 + pairingL w.1 z.2| ≤
        |pairingL z.1 w.2| + |pairingL w.1 z.2| := abs_add_le _ _
    _ ≤ ‖z.1‖ * ‖w.2‖ + ‖w.1‖ * ‖z.2‖ := by
      -- Apply the established `C0Seq`--`L1Seq` estimate to each summand.
      gcongr
      · simpa only [pairingL_apply] using abs_tsum_mul_le z.1 w.2
      · simpa only [pairingL_apply] using abs_tsum_mul_le w.1 z.2
    _ ≤ (‖z.1‖ + ‖z.2‖) * (‖w.1‖ + ‖w.2‖) := by
      -- The remaining two terms in the expanded product are nonnegative.
      nlinarith [norm_nonneg z.1, norm_nonneg z.2, norm_nonneg w.1, norm_nonneg w.2]
    _ = zSize z * zSize w := by rfl

end C0Seq
