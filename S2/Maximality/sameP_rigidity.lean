/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SamePositiveCoordinate

/-!
# Rigidity at a common Lorentz time

This module records nonpositivity and coordinate rigidity for equal positive coordinates.
-/

public section

/- Lemma 7.4a (Same-time Lorentz difference is nonpositive) (1): points with
the same positive Lorentz coordinate have difference pairing equal to the
negative squared distance between their negative coordinates. -/
#check (Lorentz.sameP_quadraticPairing :
  ∀ (d : C0Seq) (hd : d ≠ 0) (w mP : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd w = Lorentz.positiveCoordinate d hd mP →
      C0Seq.quadraticPairing (w - mP) =
        -(‖Lorentz.negativeCoordinate d hd w -
          Lorentz.negativeCoordinate d hd mP‖ ^ 2))

/- Lemma 7.4a (Same-time Lorentz difference is nonpositive) (2): the
quadratic pairing of the difference of two points at the same positive
Lorentz coordinate is nonpositive. -/
#check (Lorentz.sameP_quadraticPairing_nonpos :
  ∀ (d : C0Seq) (hd : d ≠ 0) (w mP : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd w = Lorentz.positiveCoordinate d hd mP →
      C0Seq.quadraticPairing (w - mP) ≤ 0)

/- Lemma 7.4a (Same-time Lorentz difference is nonpositive) (3): if the
difference pairing is also nonnegative, the negative Lorentz coordinates
coincide. -/
#check (Lorentz.sameP_rigidity :
  ∀ (d : C0Seq) (hd : d ≠ 0) (w mP : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd w = Lorentz.positiveCoordinate d hd mP →
      0 ≤ C0Seq.quadraticPairing (w - mP) →
        Lorentz.negativeCoordinate d hd w =
          Lorentz.negativeCoordinate d hd mP)
