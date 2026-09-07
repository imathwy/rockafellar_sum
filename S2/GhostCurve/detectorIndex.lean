/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorIndex

/-!
# Scheduled detector indices

This module exposes evaluation and convergence API for pair-indexed detector
families along the repeated detector schedule.
-/

public section

open Topology

/- Evaluate a pair-indexed detector-point family at the scheduled detector pair. -/
#check (Lorentz.scheduledDetectorPoint :
  {d : C0Seq} →
    (∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d) →
      ℕ → ℕ → Lorentz.parametrizedSubspace d)

/- The scheduled detector point evaluates at the scheduled pair. -/
#check (Lorentz.scheduledDetectorPoint_apply :
  ∀ {d : C0Seq}
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d) (i n : ℕ),
    Lorentz.scheduledDetectorPoint h i n =
      h (DetectorTriple.schedule.toFun i).p (DetectorTriple.schedule.toFun i).q
        (DetectorTriple.schedule.toFun i).p_lt_q n)

/- Pairwise convergence of negative Lorentz coordinates restricts to each
scheduled detector pair. -/
#check (Lorentz.tendsto_negativeCoordinate_scheduledDetectorPoint :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (_ : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0)) (i : ℕ),
    Filter.Tendsto
      (fun n ↦ Lorentz.negativeCoordinate d hd
        (Lorentz.scheduledDetectorPoint h i n))
      Filter.atTop (nhds 0))

/- The selected detector-index function is explicit data depending on the fixed
scale and the pairwise convergence hypotheses. -/
#check (Lorentz.detectorIndex :
  (d : C0Seq) → (hd : d ≠ 0) →
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) →
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d) →
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto
        (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) →
    ℕ → ℕ)

/- Lemma 6.10b (Diagonal detector index chosen after scaling): after fixing the
scale, every scheduled detector pair has a selected index at least its schedule
index where the scaled negative-coordinate norm is less than half the scheduled
radius. -/
#check (Lorentz.detectorIndex_spec :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0)) (i : ℕ),
    i ≤ Lorentz.detectorIndex d hd h_missing h h_tendsto i ∧
      Lorentz.detectorScale d hd h_missing i *
          ‖Lorentz.negativeCoordinate d hd
            (Lorentz.scheduledDetectorPoint h i
              (Lorentz.detectorIndex d hd h_missing h h_tendsto i))‖ <
        DetectorTriple.rightRadius i / 2)

/- Every selected detector index is at least its schedule index. -/
#check (Lorentz.le_detectorIndex :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0)) (i : ℕ),
    i ≤ Lorentz.detectorIndex d hd h_missing h h_tendsto i)

/- At the selected index, the scaled negative-coordinate norm is less than half
the scheduled radius. -/
#check (Lorentz.scaled_norm_detectorIndex_lt :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0)) (i : ℕ),
    Lorentz.detectorScale d hd h_missing i *
        ‖Lorentz.negativeCoordinate d hd
          (Lorentz.scheduledDetectorPoint h i
            (Lorentz.detectorIndex d hd h_missing h h_tendsto i))‖ <
      DetectorTriple.rightRadius i / 2)
