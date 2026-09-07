/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.LorentzCone.HilbertProd2
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.QuadraticIdentity
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.SymmetricPart

/-!
# Parametrized Lorentz energy

This module supplies the quadratic and symmetric pairing formulas for
parametrized Lorentz points.
-/

public section

open scoped InnerProductSpace

namespace Lorentz

/-- The quadratic pairing of a parametrized point is its representative-level
operator expression. -/
theorem quadraticPairing_parametrization (d : C0Seq) (a : L1Seq) (t : ℝ) :
    C0Seq.quadraticPairing (parametrization d (a, t)) =
      -(‖L1Seq.intervalCoordinateOperator a‖ ^ 2) + t * C0Seq.pairingL d a := by
  -- Expand the parametrization and distribute the dual pairing over its three terms.
  rw [parametrization_apply, C0Seq.quadraticPairing_apply]
  rw [map_add, map_smul]
  rw [map_neg]
  -- Replace the positive-operator quadratic form by the squared interval norm.
  rw [← L1Seq.positiveOperator_quadratic_eq_norm_sq]
  simp only [add_apply, neg_apply, smul_apply, smul_eq_mul]

/-- On a subspace parametrized by a nonzero vector, the quadratic pairing is
the Lorentz energy of the intrinsic coordinates. -/
theorem quadraticPairing_eq_energy (d : C0Seq) (hd : d ≠ 0)
    (z : parametrizedSubspace d) :
    C0Seq.quadraticPairing z =
      energy (positiveCoordinate d hd z, negativeCoordinate d hd z) := by
  -- Choose representative parameters for the point in the parametrized subspace.
  have hzmem := (mem_parametrizedSubspace d z.1).mp z.property
  rcases hzmem with ⟨a, t, hu⟩
  have hz : z = parametrizedPoint d a t := by
    apply Subtype.ext
    rw [parametrizedPoint_apply, parametrization_apply]
    exact hu
  subst z
  -- Rewrite all three quantities on the canonical representative and complete the square.
  rw [parametrizedPoint_apply, quadraticPairing_parametrization]
  rw [positiveCoordinate_apply, negativeCoordinate_apply]
  exact completeSquareEnergy (L1Seq.intervalCoordinateOperator a)
    (C0Seq.pairingL d a) t

/-- On a subspace parametrized by a nonzero vector, the quadratic pairing is
the square of the positive coordinate minus the squared norm of the negative
coordinate. -/
theorem quadraticIdentity (d : C0Seq) (hd : d ≠ 0) (z : parametrizedSubspace d) :
    C0Seq.quadraticPairing z =
      positiveCoordinate d hd z ^ 2 - ‖negativeCoordinate d hd z‖ ^ 2 := by
  -- Pass through Lorentz energy, whose definition is the required difference of squares.
  rw [quadraticPairing_eq_energy]
  rfl

/-- On a subspace parametrized by a nonzero vector, the symmetric quadratic
pairing is twice the Lorentz scalar product of the intrinsic coordinates. -/
theorem symmetricForm_eq_coordinates (d : C0Seq) (hd : d ≠ 0)
    (z w : parametrizedSubspace d) :
    C0Seq.symmetricForm z w =
      2 * (positiveCoordinate d hd z * positiveCoordinate d hd w -
        ⟪negativeCoordinate d hd z, negativeCoordinate d hd w⟫_ℝ) := by
  have hzmem := (mem_parametrizedSubspace d z.1).mp z.property
  have hwmem := (mem_parametrizedSubspace d w.1).mp w.property
  rcases hzmem with ⟨a, t, hzval⟩
  rcases hwmem with ⟨b, s, hwval⟩
  have hz : z = parametrizedPoint d a t := by
    apply Subtype.ext
    rw [parametrizedPoint_apply, parametrization_apply]
    exact hzval
  have hw : w = parametrizedPoint d b s := by
    apply Subtype.ext
    rw [parametrizedPoint_apply, parametrization_apply]
    exact hwval
  subst z
  subst w
  rw [parametrizedPoint_apply, parametrizedPoint_apply]
  rw [parametrization_apply, parametrization_apply,
    C0Seq.symmetricForm_apply, positiveCoordinate_apply,
    positiveCoordinate_apply, negativeCoordinate_apply,
    negativeCoordinate_apply, HilbertProd2.inner_mk]
  rw [C0Seq.pairingL.map_add, C0Seq.pairingL.map_add,
    C0Seq.pairingL.map_neg, C0Seq.pairingL.map_neg,
    C0Seq.pairingL.map_smul, C0Seq.pairingL.map_smul]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hsym_ab := congrArg
      (fun F : L1Seq →L[ℝ] StrongDual ℝ L1Seq => F a b)
      L1Seq.positiveOperator_symmetricPart
  have hsym_ab' :
      C0Seq.pairingL (L1Seq.positiveOperator a) b +
          C0Seq.pairingL (L1Seq.positiveOperator b) a =
        2 * ⟪L1Seq.intervalCoordinateOperator a,
          L1Seq.intervalCoordinateOperator b⟫_ℝ := by
    have htrans :
        (L1Seq.positiveOperator.reindexedTranspose a) b =
          C0Seq.pairingL (L1Seq.positiveOperator b) a := by
      rw [ContinuousLinearMap.reindexedTranspose_apply_apply]
      exact (C0Seq.pairingL_apply (L1Seq.positiveOperator b) a).symm
    have htmp := hsym_ab
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      two_smul, L1Seq.intervalCoordinateAdjoint_apply, htrans] at htmp
    calc
      C0Seq.pairingL (L1Seq.positiveOperator a) b +
          C0Seq.pairingL (L1Seq.positiveOperator b) a =
        ⟪L1Seq.intervalCoordinateOperator a,
          L1Seq.intervalCoordinateOperator b⟫_ℝ +
          ⟪L1Seq.intervalCoordinateOperator a,
            L1Seq.intervalCoordinateOperator b⟫_ℝ := htmp
      _ = 2 * ⟪L1Seq.intervalCoordinateOperator a,
          L1Seq.intervalCoordinateOperator b⟫_ℝ := by ring
  simp only [neg_apply]
  calc
    -(C0Seq.pairingL (L1Seq.positiveOperator a) b) +
          t * C0Seq.pairingL d b +
          (-(C0Seq.pairingL (L1Seq.positiveOperator b) a) +
            s * C0Seq.pairingL d a) =
        t * C0Seq.pairingL d b + s * C0Seq.pairingL d a -
          (C0Seq.pairingL (L1Seq.positiveOperator a) b +
            C0Seq.pairingL (L1Seq.positiveOperator b) a) := by ring
    _ = t * C0Seq.pairingL d b + s * C0Seq.pairingL d a -
          2 * ⟪L1Seq.intervalCoordinateOperator a,
            L1Seq.intervalCoordinateOperator b⟫_ℝ := by rw [hsym_ab']
    _ = 2 *
        ((t + (C0Seq.pairingL d) a) / 2 *
            ((s + (C0Seq.pairingL d) b) / 2) -
          (⟪L1Seq.intervalCoordinateOperator a,
              L1Seq.intervalCoordinateOperator b⟫_ℝ +
            (t - (C0Seq.pairingL d) a) / 2 *
              ((s - (C0Seq.pairingL d) b) / 2))) := by ring

end Lorentz
