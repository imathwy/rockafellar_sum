/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates
public import ReasLib.Analysis.Normed.LorentzCone.SeedTemplate
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/-!
# Scaled detector combinations
-/

public section

open scoped InnerProductSpace

namespace Lorentz

/-- The affine detector combination used by the seed construction. -/
noncomputable def scaledDetector {d : C0Seq} (ξ h : parametrizedSubspace d) (r : ℝ) :
    parametrizedSubspace d := ξ + r • h

/-- Positive Lorentz coordinates of a scaled detector combination expand
linearly. -/
theorem positiveCoordinate_scaledDetector {d : C0Seq} (hd : d ≠ 0)
    (ξ h : parametrizedSubspace d) (r : ℝ) :
    positiveCoordinate d hd (scaledDetector ξ h r) =
      positiveCoordinate d hd ξ + r * positiveCoordinate d hd h := by
  unfold scaledDetector
  rw [map_add, map_smul]
  simp only [smul_eq_mul]

/-- Negative Lorentz coordinates of a scaled detector combination expand
linearly. -/
theorem negativeCoordinate_scaledDetector {d : C0Seq} (hd : d ≠ 0)
    (ξ h : parametrizedSubspace d) (r : ℝ) :
    negativeCoordinate d hd (scaledDetector ξ h r) =
      negativeCoordinate d hd ξ + r • negativeCoordinate d hd h := by
  unfold scaledDetector
  rw [map_add, map_smul]

/-- The quadratic pairing of a scaled detector combination has the intrinsic
Lorentz energy expansion. -/
theorem quadraticPairing_scaledDetector_expansion {d : C0Seq} (hd : d ≠ 0)
    (ξ h : parametrizedSubspace d) (r : ℝ) :
    C0Seq.quadraticPairing (scaledDetector ξ h r) =
      C0Seq.quadraticPairing ξ +
        2 * r * (positiveCoordinate d hd ξ * positiveCoordinate d hd h -
          ⟪negativeCoordinate d hd ξ, negativeCoordinate d hd h⟫_ℝ) +
        r ^ 2 * C0Seq.quadraticPairing h := by
  rw [quadraticIdentity d hd]
  rw [positiveCoordinate_scaledDetector, negativeCoordinate_scaledDetector]
  rw [quadraticIdentity d hd ξ, quadraticIdentity d hd h]
  exact energy_add_smul_expansion
    (positiveCoordinate d hd ξ, negativeCoordinate d hd ξ)
    (positiveCoordinate d hd h, negativeCoordinate d hd h) r

end Lorentz
