/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Sequence.L1.Relocation

/-!
# Remote copies of finitely supported sequences

This module exposes the remote-copy construction together with its coordinate,
support, and norm formulas.
-/

#check (L1Seq.remoteCopy :
  (b : L1Seq) → (fun i ↦ b i).HasFiniteSupport → (ℕ → ℕ) → L1Seq)

#check (L1Seq.remoteCopy_apply :
  ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ) (j : ℕ),
    L1Seq.remoteCopy b h_b m j =
      ∑ i ∈ h_b.toFinset, if m i = j then b i else 0)

#check (L1Seq.remoteCopy_apply_of_mem_support :
  ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ),
    Set.InjOn m (Function.support fun i ↦ b i) →
      ∀ (i : ℕ), b i ≠ 0 → L1Seq.remoteCopy b h_b m (m i) = b i)

#check (L1Seq.support_remoteCopy :
  ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ),
    Set.InjOn m (Function.support fun i ↦ b i) →
      Function.support (fun j ↦ L1Seq.remoteCopy b h_b m j) =
        m '' Function.support (fun i ↦ b i))

#check (L1Seq.support_remoteCopy_subset_Ioi :
  ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ),
    Set.InjOn m (Function.support fun i ↦ b i) → ∀ (N : ℕ),
      (∀ i, b i ≠ 0 → N < m i) →
        Function.support (fun j ↦ L1Seq.remoteCopy b h_b m j) ⊆ Set.Ioi N)

#check (L1Seq.norm_remoteCopy :
  ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ),
    Set.InjOn m (Function.support fun i ↦ b i) →
      ‖L1Seq.remoteCopy b h_b m‖ = ‖b‖)
