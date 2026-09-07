/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.DenseRange

/-!
# Fixed-positive Lorentz coordinates

This module adjusts the parametrization parameter to prescribe a positive
Lorentz coordinate.
-/

public section

namespace Lorentz

/-- Choosing `t = 2 * p - C0Seq.pairingL d a` makes the positive Lorentz
coordinate of `parametrizedPoint d a t` equal to `p`. -/
theorem positiveCoordinate_adjustedParameter (d : C0Seq) (hd : d ≠ 0)
    (a : L1Seq) (p : ℝ) :
    positiveCoordinate d hd
        (parametrizedPoint d a (2 * p - C0Seq.pairingL d a)) = p := by
  -- Evaluate the positive coordinate, then cancel the pairing terms.
  rw [positiveCoordinate_apply]
  ring

/-- The negative Lorentz coordinate at the parameter adjusted to prescribe its
positive coordinate. -/
theorem negativeCoordinate_adjustedParameter (d : C0Seq) (hd : d ≠ 0)
    (a : L1Seq) (p : ℝ) :
    negativeCoordinate d hd
        (parametrizedPoint d a (2 * p - C0Seq.pairingL d a)) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        (p - C0Seq.pairingL d a) := by
  -- Evaluate the negative coordinate and normalize its scalar component.
  rw [negativeCoordinate_apply]
  congr 1
  ring

/-- The first ambient coordinate of the point with its parameter adjusted to
prescribe the positive Lorentz coordinate. -/
theorem parametrizedPoint_fst_adjustedParameter (d : C0Seq) (a : L1Seq) (p : ℝ) :
    (parametrizedPoint d a (2 * p - C0Seq.pairingL d a) :
      C0Seq × L1Seq).1 =
      -L1Seq.positiveOperator a + (2 * p - C0Seq.pairingL d a) • d := by
  -- Project the parametrized point and use the parametrization formula.
  rw [parametrizedPoint_apply, parametrization_apply]

/-- A point can have any prescribed positive Lorentz coordinate while its first
ambient coordinate and negative Lorentz coordinate simultaneously approximate
prescribed targets. -/
theorem exists_approx_fixedPositiveCoordinate
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (p : ℝ) (x₀ : C0Seq) (v : UnitL2) (r ε : ℝ) (hε : 0 < ε) :
    ∃ z : parametrizedSubspace d,
      positiveCoordinate d hd z = p ∧
      ‖(z : C0Seq × L1Seq).1 - x₀‖ < ε ∧
      ‖negativeCoordinate d hd z - HilbertProd2.mk v r‖ < ε := by
  -- Reserve one common tolerance for the three dense-coordinate errors.
  let δ : ℝ := ε / (4 * (‖d‖ + 1))
  have hden : 0 < 4 * (‖d‖ + 1) := by
    positivity
  have hδ : 0 < δ := by
    exact div_pos hε hden
  have hscale : δ * (‖d‖ + 1) = ε / 4 := by
    dsimp only [δ]
    field_simp [ne_of_gt hden]
  have hambient_budget : δ + δ * ‖d‖ < ε := by
    have hrewrite : δ + δ * ‖d‖ = δ * (‖d‖ + 1) := by ring
    rw [hrewrite, hscale]
    linarith
  have hproduct_budget : δ + δ < ε := by
    have hδ_le : δ ≤ ε / 4 := by
      nlinarith [mul_nonneg hδ.le (norm_nonneg d)]
    linarith
  -- Approximate the three source coordinates simultaneously at the reduced tolerance.
  obtain ⟨a, hA, hV, hpair⟩ :=
    L1Seq.exists_a_approx_target_triple d h_missing p x₀ v r δ hδ
  have hpair' : ‖(p - r) - C0Seq.pairingL d a‖ < δ := by
    simpa only [norm_sub_rev] using hpair
  refine ⟨parametrizedPoint d a (2 * p - C0Seq.pairingL d a), ?_, ?_, ?_⟩
  · -- The adjusted parameter fixes the positive coordinate exactly.
    exact positiveCoordinate_adjustedParameter d hd a p
  · -- Split the ambient error into the `A`-error and the pairing error along `d`.
    rw [parametrizedPoint_fst_adjustedParameter]
    have hambient_decomp :
        -L1Seq.positiveOperator a + (2 * p - C0Seq.pairingL d a) • d - x₀ =
          -(L1Seq.positiveOperator a - ((p + r) • d - x₀)) +
            ((p - r) - C0Seq.pairingL d a) • d := by
      module
    rw [hambient_decomp]
    calc
      ‖-(L1Seq.positiveOperator a - ((p + r) • d - x₀)) +
          ((p - r) - C0Seq.pairingL d a) • d‖
          ≤ ‖L1Seq.positiveOperator a - ((p + r) • d - x₀)‖ +
              ‖(p - r) - C0Seq.pairingL d a‖ * ‖d‖ := by
            simpa only [norm_neg, norm_smul] using
              norm_add_le
                (-(L1Seq.positiveOperator a - ((p + r) • d - x₀)))
                (((p - r) - C0Seq.pairingL d a) • d)
      _ < δ + δ * ‖d‖ := by
        exact add_lt_add hA (mul_lt_mul_of_pos_right hpair' (norm_pos_iff.mpr hd))
      _ < ε := hambient_budget
  · -- Split the negative-coordinate error into its two Hilbert-product axes.
    rw [negativeCoordinate_adjustedParameter]
    have hnegative_decomp :
        HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
              (p - C0Seq.pairingL d a) - HilbertProd2.mk v r =
          HilbertProd2.mk (L1Seq.intervalCoordinateOperator a - v) 0 +
            HilbertProd2.mk 0 ((p - C0Seq.pairingL d a) - r) := by
      apply HilbertProd2.ext
      · simp [HilbertProd2.fst, HilbertProd2.mk]
      · simp [HilbertProd2.snd, HilbertProd2.mk]
    have hpair_coordinate :
        (p - C0Seq.pairingL d a) - r =
          (p - r) - C0Seq.pairingL d a := by
      ring
    rw [hnegative_decomp]
    calc
      ‖HilbertProd2.mk (L1Seq.intervalCoordinateOperator a - v) 0 +
          HilbertProd2.mk 0 ((p - C0Seq.pairingL d a) - r)‖
          ≤ ‖HilbertProd2.mk (L1Seq.intervalCoordinateOperator a - v) 0‖ +
              ‖HilbertProd2.mk 0 ((p - C0Seq.pairingL d a) - r)‖ :=
            norm_add_le _ _
      _ = ‖L1Seq.intervalCoordinateOperator a - v‖ +
          ‖(p - C0Seq.pairingL d a) - r‖ := by
            simp only [HilbertProd2.mk, WithLp.norm_toLp_fst,
              WithLp.norm_toLp_snd]
      _ < δ + δ := by
        rw [hpair_coordinate]
        exact add_lt_add hV hpair'
      _ < ε := hproduct_budget

/-- A nonzero sequence outside the range of the positive operator admits a
parametrized point with positive coordinate `1` and uniformly small negative
and first ambient coordinates. -/
theorem exists_futureRayBase (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) :
    ∃ v : parametrizedSubspace d,
      positiveCoordinate d hd v = 1 ∧
      ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16 ∧
      ‖(v : C0Seq × L1Seq).1‖ < (1 : ℝ) / 8 := by
  -- Specialize simultaneous approximation to the two zero targets.
  have htol : 0 < (1 : ℝ) / 16 := by
    norm_num
  obtain ⟨v, hpositive, hambient, hnegative⟩ :=
    exists_approx_fixedPositiveCoordinate d hd h_missing
      1 0 0 0 ((1 : ℝ) / 16) htol
  -- Identify the constructed Hilbert-product target with zero.
  have hzero : HilbertProd2.mk (0 : UnitL2) 0 = 0 := by
    apply HilbertProd2.ext
    · rw [HilbertProd2.fst_mk]
      rfl
    · rw [HilbertProd2.snd_mk]
      rfl
  have hnegative' :
      ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16 := by
    simpa only [hzero, sub_zero] using hnegative
  -- The ambient estimate returned at radius `1 / 16` is stronger than required.
  have hambient' : ‖(v : C0Seq × L1Seq).1‖ < (1 : ℝ) / 16 := by
    simpa only [sub_zero] using hambient
  have htol_lt : (1 : ℝ) / 16 < (1 : ℝ) / 8 := by
    norm_num
  exact ⟨v, hpositive, hnegative', lt_trans hambient' htol_lt⟩

end Lorentz
