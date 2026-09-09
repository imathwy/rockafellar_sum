/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector

/-!
# Exact finite detector points
-/

public section

namespace Lorentz

/-- The finite detector point with prescribed zero positive coordinate. -/
noncomputable def finiteDetectorPoint (d : C0Seq) (p q : ℕ) : parametrizedSubspace d :=
  parametrizedPoint d (L1Seq.twoDet d p q)
    (-C0Seq.pairingL d (L1Seq.twoDet d p q))

/-- The finite detector point has zero positive Lorentz coordinate. -/
theorem positiveCoordinate_finiteDetectorPoint
    (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) :
    positiveCoordinate d hd (finiteDetectorPoint d p q) = 0 := by
  unfold finiteDetectorPoint
  rw [positiveCoordinate_apply]
  ring

/-- Its negative coordinate is the interval-coordinate detector vector together
with the residual scalar pairing. -/
theorem negativeCoordinate_finiteDetectorPoint
    (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) :
    negativeCoordinate d hd (finiteDetectorPoint d p q) =
      HilbertProd2.mk
        (L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q))
        (-C0Seq.pairingL d (L1Seq.twoDet d p q)) := by
  unfold finiteDetectorPoint
  rw [negativeCoordinate_apply]
  congr 1
  ring

end Lorentz
