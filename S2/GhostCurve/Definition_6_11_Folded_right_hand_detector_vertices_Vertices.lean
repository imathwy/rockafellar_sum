/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex

/-!
# Folded Detector Vertex API

This module exposes the canonical folded perturbation and vertex declarations.
-/

section

variable (d : C0Seq) (hd : d ≠ 0)
  (h_missing : d ∉ Set.range L1Seq.positiveOperator)
  (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
  (h_tendsto : ∀ p q (h_pq : p < q),
    Filter.Tendsto
      (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
      Filter.atTop (nhds 0))
  (i : ℕ)

#check (Lorentz.detectorPerturbation d hd h_missing h h_tendsto :
  ℕ → Lorentz.parametrizedSubspace d)
#check (Lorentz.detectorPerturbation_apply d hd h_missing h h_tendsto i :
  Lorentz.detectorPerturbation d hd h_missing h h_tendsto i =
    (((DetectorTriple.schedule.toFun i).sign : ℝ) *
      Lorentz.detectorScale d hd h_missing i) •
        Lorentz.scheduledDetectorPoint h i
          (Lorentz.detectorIndex d hd h_missing h h_tendsto i))
#check (Lorentz.rightVertex d hd h_missing h h_tendsto :
  ℕ → Lorentz.parametrizedSubspace d)
#check (Lorentz.rightVertex_apply d hd h_missing h h_tendsto i :
  Lorentz.rightVertex d hd h_missing h h_tendsto i =
    Lorentz.nearGhostBase d hd h_missing i +
      Lorentz.detectorPerturbation d hd h_missing h h_tendsto i)
#check (Lorentz.rightVertex_mem d hd h_missing h h_tendsto i :
  (Lorentz.rightVertex d hd h_missing h h_tendsto i : C0Seq × L1Seq) ∈
    Lorentz.parametrizedSubspace d)

end
