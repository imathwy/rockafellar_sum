/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator.ConstraintQualification

/-!
# Classical Interior Constraint Qualification

This module exposes the domain and interior witness for the fixed constraint.
-/

public section

namespace Lorentz

/- Lemma 7.11 (The classical interior constraint qualification) (1):
the primal coordinate of `(2 : ℝ) • v` lies in the domain of the ghost-curve
operator. -/
#check (Lorentz.two_smul_primal_mem_ghostCurveOperator_dom :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d), positiveCoordinate d hd v = 1 →
      ((2 : ℝ) • v).1.1 ∈
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).dom)

/- Lemma 7.11 (The classical interior constraint qualification) (2):
the primal coordinate of `(2 : ℝ) • v` has norm less than `1 / 4` when the
primal coordinate of `v` has norm less than `1 / 8`. -/
#check (Lorentz.norm_two_smul_primal_lt_quarter :
  ∀ (d : C0Seq) (v : parametrizedSubspace d),
    ‖v.1.1‖ < (1 : ℝ) / 8 → ‖((2 : ℝ) • v).1.1‖ < (1 : ℝ) / 4)

/- Lemma 7.11 (The classical interior constraint qualification) (3):
the same concrete primal point lies in the operator domain intersected with the
interior of `C0Seq.finalConstraint`. -/
#check (Lorentz.two_smul_primal_mem_constraintQualification :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d), positiveCoordinate d hd v = 1 →
      ‖v.1.1‖ < (1 : ℝ) / 8 →
        ((2 : ℝ) • v).1.1 ∈
          (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).dom ∩
            interior C0Seq.finalConstraint)

/- The concrete witness also yields the nonempty-intersection formulation of
the constraint qualification. -/
#check (Lorentz.ghostCurveOperator_constraintQualification :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d), positiveCoordinate d hd v = 1 →
      ‖v.1.1‖ < (1 : ℝ) / 8 →
        Set.Nonempty
          ((ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).dom ∩
            interior C0Seq.finalConstraint))

end Lorentz
