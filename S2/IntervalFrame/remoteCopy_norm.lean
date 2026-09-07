/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Sequence.L1.Relocation

/-!
# Support and norm of remote copies

This module exposes support relocation and norm preservation for injective
remote copies of finitely supported `L1Seq` vectors.
-/

/- Lemma 2.12b (Norm-preserving copied coefficient vector) (1):
the copied vector is supported strictly above the prescribed cutoff. -/
#check (L1Seq.support_remoteCopy_subset_Ioi :
  ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ),
    Set.InjOn m (Function.support fun i ↦ b i) → ∀ (N : ℕ),
      (∀ i, b i ≠ 0 → N < m i) →
        Function.support (fun j ↦ L1Seq.remoteCopy b h_b m j) ⊆ Set.Ioi N)

/- Lemma 2.12b (Norm-preserving copied coefficient vector) (2):
the copied vector has exactly the same `L1Seq` norm as its source. -/
#check (L1Seq.norm_remoteCopy :
  ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ),
    Set.InjOn m (Function.support fun i ↦ b i) →
      ‖L1Seq.remoteCopy b h_b m‖ = ‖b‖)
