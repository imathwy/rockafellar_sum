module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.ProductPairing

public section

/- The symmetric product pairing is a continuous bilinear map. -/
#check (C0Seq.prodPairingL :
  (C0Seq × L1Seq) →L[ℝ] (C0Seq × L1Seq) →L[ℝ] ℝ)

/- The symmetric product pairing is the sum of the two crossed coordinate pairings. -/
#check (C0Seq.prodPairingL_apply :
  ∀ z w : C0Seq × L1Seq,
    C0Seq.prodPairingL z w =
      C0Seq.pairingL z.1 w.2 + C0Seq.pairingL w.1 z.2)

/- Infrastructure A.15 (An explicit one-norm size on the primal-dual product) (1):
the size of a primal-dual point is the sum of its coordinate norms. -/
#check (C0Seq.zSize : (C0Seq × L1Seq) → ℝ)

/- The size of an explicit primal-dual pair is the sum of its two norms. -/
#check (C0Seq.zSize_apply :
  ∀ (x : C0Seq) (a : L1Seq), C0Seq.zSize (x, a) = ‖x‖ + ‖a‖)

/- The explicit size is the canonical `WithLp 1` product norm. -/
#check (C0Seq.zSize_eq_norm_toLp :
  ∀ z : C0Seq × L1Seq, C0Seq.zSize z = ‖WithLp.toLp 1 z‖)

/- Infrastructure A.15 (An explicit one-norm size on the primal-dual product) (2):
the explicit size satisfies the triangle inequality. -/
#check (C0Seq.zSize_add_le :
  ∀ z w : C0Seq × L1Seq,
    C0Seq.zSize (z + w) ≤ C0Seq.zSize z + C0Seq.zSize w)

/- Infrastructure A.15 (An explicit one-norm size on the primal-dual product) (3):
the explicit size is absolutely homogeneous under real scalar multiplication. -/
#check (C0Seq.zSize_smul :
  ∀ (c : ℝ) (z : C0Seq × L1Seq),
    C0Seq.zSize (c • z) = |c| * C0Seq.zSize z)

/- Infrastructure A.15 (An explicit one-norm size on the primal-dual product) (4):
the symmetric cross-pairing is bounded by the product of the explicit sizes. -/
#check (C0Seq.abs_prodPairingL_le :
  ∀ z w : C0Seq × L1Seq,
    |C0Seq.prodPairingL z w| ≤ C0Seq.zSize z * C0Seq.zSize w)
