/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.TwoCoordinateDeterminant

/-!
# Detector functionals

This module defines continuous detector functionals built from two-coordinate
determinant vectors.
-/

@[expose] public section

noncomputable section

namespace Lorentz

/-- The continuous linear functional sending `(x, u)` to the pairing of
`x + L1Seq.positiveOperator u` with `L1Seq.twoDet d p q`. -/
noncomputable def detectorFunctional (d : C0Seq) (p q : ℕ) :
    (C0Seq × L1Seq) →L[ℝ] ℝ :=
  (C0Seq.pairingL.flip (L1Seq.twoDet d p q)).comp
    ((ContinuousLinearMap.fst ℝ C0Seq L1Seq) +
      L1Seq.positiveOperator.comp (ContinuousLinearMap.snd ℝ C0Seq L1Seq))

/-- Evaluation of `detectorFunctional` recovers its defining two-coordinate pairing. -/
@[simp]
theorem detectorFunctional_apply (d : C0Seq) (p q : ℕ) (x : C0Seq) (u : L1Seq) :
    detectorFunctional d p q (x, u) =
      C0Seq.pairingL (x + L1Seq.positiveOperator u) (L1Seq.twoDet d p q) := by
  -- Reduce the composed detector and both product projections to their values.
  rfl

/-- Every point outside `parametrizedSubspace d`, for nonzero `d`, has a nonzero
reading under some ordered two-coordinate detector functional. -/
theorem exists_detectorFunctional_ne_zero (d : C0Seq) (w : C0Seq × L1Seq)
    (hd : d ≠ 0) (hw : w ∉ parametrizedSubspace d) :
    ∃ p q : ℕ, p < q ∧ detectorFunctional d p q w ≠ 0 := by
  rcases w with ⟨x, u⟩
  -- Exclusion from the parametrized subspace forces the residual outside the span of `d`.
  have hresidual : x + L1Seq.positiveOperator u ∉ ℝ ∙ d := by
    intro hspan
    exact hw ((mk_mem_parametrizedSubspace_iff d x u).mpr hspan)
  -- Detect that residual on two coordinates and rewrite the pairing as the detector reading.
  obtain ⟨p, q, hpq, hpair⟩ :=
    C0Seq.exists_pairingL_twoDet_ne_zero d (x + L1Seq.positiveOperator u) hd hresidual
  refine ⟨p, q, hpq, ?_⟩
  simpa only [detectorFunctional_apply] using hpair

end Lorentz
