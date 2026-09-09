/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.UnitDifferenceDetector
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Single

/-!
# Fixed-positive seed bases
-/

public section

namespace Lorentz

/-- The carrier point obtained from a source sequence `a` with prescribed
positive Lorentz coordinate `s`. -/
noncomputable def seedBase {d : C0Seq} (a : L1Seq) (s : ℝ) : parametrizedSubspace d :=
  parametrizedPoint d a (2 * s - C0Seq.pairingL d a)

/-- The seed base has exactly the prescribed positive coordinate. -/
theorem positiveCoordinate_seedBase {d : C0Seq} (hd : d ≠ 0)
    (a : L1Seq) (s : ℝ) :
    positiveCoordinate d hd (seedBase a s) = s := by
  unfold seedBase
  exact positiveCoordinate_adjustedParameter d hd a s

/-- The negative coordinate of a seed base is the interval-coordinate image
and the adjusted scalar residual. -/
theorem negativeCoordinate_seedBase {d : C0Seq} (hd : d ≠ 0)
    (a : L1Seq) (s : ℝ) :
    negativeCoordinate d hd (seedBase a s) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        (s - C0Seq.pairingL d a) := by
  unfold seedBase
  exact negativeCoordinate_adjustedParameter d hd a s

/-- The seed base at a zero source sequence is the positive axis point. -/
theorem seedBase_zero (d : C0Seq) (s : ℝ) :
    seedBase (0 : L1Seq) s = parametrizedPoint d 0 (2 * s) := by
  unfold seedBase
  simp

/-- The canonical first-axis direction used by the S3 construction. -/
def axisDirection : C0Seq := c0Single 1 1

/-- The axis direction pairs with a unit difference at coordinate `1` as one
when the second coordinate is distinct. -/
theorem pairingL_axisDirection_unitDifference {r : ℕ} (hr : r ≠ 1) :
    C0Seq.pairingL axisDirection (unitDifference 1 r) = 1 := by
  rw [pairingL_unitDifference]
  simp [axisDirection, c0Single_apply, hr]

end Lorentz
