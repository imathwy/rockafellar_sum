module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

public section

/- Infrastructure A.7 (The bundled c₀–ℓ¹ dual pairing): the coordinatewise
pairing, bundled as continuous linear maps in the `C0Seq` and `L1Seq` variables. -/
#check (C0Seq.pairingL : C0Seq →L[ℝ] L1Seq →L[ℝ] ℝ)

#check (C0Seq.pairingL_apply : ∀ (x : C0Seq) (a : L1Seq),
  C0Seq.pairingL x a = ∑' n : ℕ, x n * a n)

#check (C0Seq.pairingL_flip_apply : ∀ (a : L1Seq) (x : C0Seq),
  C0Seq.pairingL.flip a x = ∑' n : ℕ, x n * a n)

#check (C0Seq.norm_pairingL_le : ‖C0Seq.pairingL‖ ≤ 1)
