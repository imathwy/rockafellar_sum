/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.TwoCoordinateDeterminant

/-!
# Two-Coordinate Detection

This module exposes detection of vectors outside the span of a nonzero direction.
-/

public section

/- Lemma 5.4 (Two-coordinate detection of nonmultiples of $d$): if `r` does not lie
on the real line spanned by a nonzero `d`, then some ordered coordinate pair gives a
nonzero pairing with `L1Seq.twoDet d p q`; `C0Seq.pairingL_twoDet` identifies this
pairing with `d p * r q - d q * r p`. -/
#check (C0Seq.exists_pairingL_twoDet_ne_zero :
  ∀ (d r : C0Seq), d ≠ 0 → r ∉ ℝ ∙ d →
    ∃ p q : ℕ, p < q ∧ C0Seq.pairingL r (L1Seq.twoDet d p q) ≠ 0)
