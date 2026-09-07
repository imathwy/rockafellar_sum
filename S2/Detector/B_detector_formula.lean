/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Pairing
public import S2.Detector.Definition_5_8_Asymptotically_zero_Lorentz_detector_points

/-!
# Expanded detector pairing formula

This source-facing module records the canonical detector pairing identity used
in the proof of Lemma 5.10.
-/

public section

open scoped InnerProductSpace

/- Lemma 5.10a (Expanded detector pairing formula): for `w = (x, u)` and
`h = Ψ(a, -C0Seq.pairingL d a)`, the symmetric pairing expands into the detector,
interval-coordinate, and `d`-pairing terms. -/
#check (Lorentz.detectorPairingFormula :
  ∀ (d x : C0Seq) (u a : L1Seq),
    C0Seq.symmetricForm (x, u)
        (Lorentz.parametrization d (a, -C0Seq.pairingL d a)) =
      C0Seq.pairingL (x + L1Seq.positiveOperator u) a -
        2 * ⟪L1Seq.intervalCoordinateOperator u,
          L1Seq.intervalCoordinateOperator a⟫_ℝ -
        C0Seq.pairingL d u * C0Seq.pairingL d a)
