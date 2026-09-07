/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Data.Real.Sign
public import ReasLib.Combinatorics.DetectorTriple
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector

/-!
# Favorable detector signs

This module chooses an ordered detector pair and sign with positive reading for
points outside a parametrized subspace.
-/

@[expose] public section

namespace Lorentz

/-- A point outside `parametrizedSubspace d` has an ordered detector pair and a
real sign in `{-1, 1}` for which the signed detector reading is positive. -/
theorem exists_detectorFunctional_sign_pos (d : C0Seq) (w : C0Seq × L1Seq)
    (hd : d ≠ 0) (hw : w ∉ parametrizedSubspace d) :
    ∃ p q : ℕ, ∃ σ : ℝ,
      p < q ∧ (σ = -1 ∨ σ = 1) ∧ 0 < σ * detectorFunctional d p q w := by
  -- First choose an ordered pair on which the detector reading is nonzero.
  obtain ⟨p, q, hpq, hdet⟩ := exists_detectorFunctional_ne_zero d w hd hw
  -- Its real sign is one of the two allowed values and makes the reading positive.
  refine ⟨p, q, Real.sign (detectorFunctional d p q w), hpq, ?_, ?_⟩
  · exact Real.sign_apply_eq_of_ne_zero _ hdet
  · exact Real.sign_mul_pos_of_ne_zero _ hdet

/-- A point outside `parametrizedSubspace d` admits a detector triple whose
signed detector reading is positive. -/
theorem exists_detectorTriple_pos (d : C0Seq) (w : C0Seq × L1Seq)
    (hd : d ≠ 0) (hw : w ∉ parametrizedSubspace d) :
    ∃ t : DetectorTriple,
      0 < (t.sign : ℝ) * detectorFunctional d t.p t.q w := by
  -- Choose favorable coordinates and split according to the resulting real sign.
  obtain ⟨p, q, σ, hpq, hσ, hpos⟩ :=
    exists_detectorFunctional_sign_pos d w hd hw
  rcases hσ with hσ | hσ
  · -- Store the negative sign as the canonical negative integer unit.
    subst σ
    refine ⟨DetectorTriple.ofIndices p q hpq (-1), ?_⟩
    simpa only [DetectorTriple.p_ofIndices, DetectorTriple.q_ofIndices,
      DetectorTriple.sign_ofIndices, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one] using hpos
  · -- Store the positive sign as the canonical positive integer unit.
    subst σ
    refine ⟨DetectorTriple.ofIndices p q hpq 1, ?_⟩
    simpa only [DetectorTriple.p_ofIndices, DetectorTriple.q_ofIndices,
      DetectorTriple.sign_ofIndices, Units.val_one, Int.cast_one] using hpos

end Lorentz
