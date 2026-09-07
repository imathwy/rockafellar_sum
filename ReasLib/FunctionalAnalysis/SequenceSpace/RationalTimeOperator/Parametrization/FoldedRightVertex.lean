/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorIndex

/-!
# Folded right vertices

This module defines the signed and scaled detector perturbations used on the
right side of the ghost curve.
-/

public section

namespace Lorentz

/-- The signed, scaled detector perturbation at each scheduled detector triple. -/
noncomputable def detectorPerturbation (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) : ℕ → parametrizedSubspace d :=
  fun i ↦
    (((DetectorTriple.schedule.toFun i).sign : ℝ) *
      detectorScale d hd h_missing i) •
        scheduledDetectorPoint h i
          (detectorIndex d hd h_missing h h_tendsto i)

/-- The detector perturbation is the scheduled point multiplied by its signed scale. -/
theorem detectorPerturbation_apply (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    detectorPerturbation d hd h_missing h h_tendsto i =
      (((DetectorTriple.schedule.toFun i).sign : ℝ) *
        detectorScale d hd h_missing i) •
          scheduledDetectorPoint h i
            (detectorIndex d hd h_missing h h_tendsto i) := by
  -- Unfolding the perturbation exposes exactly the scheduled signed scaling.
  rfl

/-- The sequence of right vertices obtained by adding each detector perturbation
to its near-ghost base point. -/
noncomputable def rightVertex (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) : ℕ → parametrizedSubspace d :=
  fun i ↦ nearGhostBase d hd h_missing i +
    detectorPerturbation d hd h_missing h h_tendsto i

/-- A right vertex is its near-ghost base point plus its detector perturbation. -/
theorem rightVertex_apply (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    rightVertex d hd h_missing h h_tendsto i =
      nearGhostBase d hd h_missing i +
        detectorPerturbation d hd h_missing h h_tendsto i := by
  -- Unfolding the vertex exposes its base point and perturbation summands.
  rfl

/-- The ambient value of each right vertex lies in the parametrized subspace. -/
theorem rightVertex_mem (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    (rightVertex d hd h_missing h h_tendsto i : C0Seq × L1Seq) ∈
      parametrizedSubspace d := by
  -- The submodule-valued vertex already stores the required membership proof.
  exact (rightVertex d hd h_missing h h_tendsto i).property

end Lorentz
