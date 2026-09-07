/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Dual

/-!
# The isometric map from `L1Seq` to the dual of `C0Seq`

This module exposes the isometric coordinate-pairing map and its underlying
continuous linear map.
-/

#check (C0Seq.norm_pairingL_flip : ∀ a : L1Seq, ‖C0Seq.pairingL.flip a‖ = ‖a‖)
#check (C0Seq.l1ToDual : L1Seq →ₗᵢ[ℝ] StrongDual ℝ C0Seq)
#check (C0Seq.l1ToDual_apply : ∀ (a : L1Seq) (x : C0Seq),
  C0Seq.l1ToDual a x = ∑' n : ℕ, x n * a n)
#check (C0Seq.l1ToDual_toContinuousLinearMap :
  C0Seq.l1ToDual.toContinuousLinearMap = C0Seq.pairingL.flip)
