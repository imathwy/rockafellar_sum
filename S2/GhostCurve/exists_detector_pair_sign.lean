/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector.FavorableSign

/-!
# Favorable Detector Pairs

This module exposes detector pairs and signs with positive readings.
-/

@[expose] public section

/- Lemma 6.13a (Detector pair and favorable sign for an exterior point): a point
outside `parametrizedSubspace d` has an ordered detector pair and a sign in
`{-1, 1}` for which the signed detector reading is positive. -/
#check (Lorentz.exists_detectorFunctional_sign_pos :
  ∀ (d : C0Seq) (w : C0Seq × L1Seq), d ≠ 0 →
    w ∉ Lorentz.parametrizedSubspace d →
      ∃ p q : ℕ, ∃ σ : ℝ,
        p < q ∧ (σ = -1 ∨ σ = 1) ∧
          0 < σ * Lorentz.detectorFunctional d p q w)

/- The favorable detector pair and sign can equivalently be packaged as a
`DetectorTriple`. -/
#check (Lorentz.exists_detectorTriple_pos :
  ∀ (d : C0Seq) (w : C0Seq × L1Seq), d ≠ 0 →
    w ∉ Lorentz.parametrizedSubspace d →
      ∃ t : DetectorTriple,
        0 < (t.sign : ℝ) * Lorentz.detectorFunctional d t.p t.q w)
