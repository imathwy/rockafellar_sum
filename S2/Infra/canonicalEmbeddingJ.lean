/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

/-!
# Canonical embedding of `C0Seq`

This module exposes the coordinatewise pairing embedding of `C0Seq` into the
strong dual of `L1Seq`.
-/

public section

/- Infrastructure A.8 (Canonical embedding of c₀ into the dual of ℓ¹) (1):
the canonical map is the bundled coordinatewise pairing. -/
#check (C0Seq.pairingL : C0Seq →L[ℝ] StrongDual ℝ L1Seq)

/- Infrastructure A.8 (Canonical embedding of c₀ into the dual of ℓ¹) (2):
the canonical map evaluates as the coordinatewise pairing. -/
#check (C0Seq.pairingL_apply :
  ∀ (x : C0Seq) (a : L1Seq),
    C0Seq.pairingL x a = ∑' n : ℕ, x n * a n)

/- Infrastructure A.8 (Canonical embedding of c₀ into the dual of ℓ¹) (3):
the canonical coordinatewise pairing embeds `C0Seq` into the strong dual of `L1Seq`. -/
#check (C0Seq.pairingL_injective : Function.Injective C0Seq.pairingL)

/- Infrastructure A.8 (Canonical embedding of c₀ into the dual of ℓ¹) (4):
the image of a standard coordinate vector is scaled coordinate evaluation. -/
#check (C0Seq.pairingL_c0Single_apply :
  ∀ (n : ℕ) (r : ℝ) (a : L1Seq),
    C0Seq.pairingL (c0Single n r) a = r * a n)
