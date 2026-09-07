/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.TwoCoordinateDeterminant

/-!
# Determinant-vector API

This source-facing module records the canonical support and pairing identities
for two-coordinate determinant vectors.
-/

#check (L1Seq.twoDet : C0Seq → ℕ → ℕ → L1Seq)
#check (L1Seq.twoDet_apply :
  ∀ (d : C0Seq) (p q n : ℕ),
    L1Seq.twoDet d p q n =
      (if q = n then d p else 0) - (if p = n then d q else 0))
#check (L1Seq.support_twoDet_subset :
  ∀ (d : C0Seq) (p q : ℕ),
    Function.support (fun n ↦ L1Seq.twoDet d p q n) ⊆ ({p, q} : Set ℕ))
#check (L1Seq.twoDet_hasFiniteSupport :
  ∀ (d : C0Seq) (p q : ℕ),
    (fun n ↦ L1Seq.twoDet d p q n).HasFiniteSupport)
#check (C0Seq.pairingL_twoDet :
  ∀ (x d : C0Seq) (p q : ℕ),
    C0Seq.pairingL x (L1Seq.twoDet d p q) = d p * x q - d q * x p)
