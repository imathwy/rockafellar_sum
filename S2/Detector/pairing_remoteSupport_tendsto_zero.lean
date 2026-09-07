/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing.RemoteSupport

/-!
# Pairing limits for remote support

This module records vanishing pairings between `C0Seq` and `L1Seq` on escaping supports.
-/

public section

open Topology

/- Lemma 5.7a (c₀ vectors do not see uniformly bounded remote ℓ¹ mass): if an
`L1Seq`-valued sequence has support strictly above its index and is uniformly
bounded in norm, then its pairing with every `C0Seq` tends to zero. Taking
`x := d` gives the stated particular case. -/
#check (C0Seq.pairingL_tendsto_zero_of_support_Ioi :
  (c : ℕ → L1Seq) → (C : ℝ) →
    (∀ n, Function.support (fun m ↦ c n m) ⊆ Set.Ioi n) →
    (∀ n, ‖c n‖ ≤ C) → (x : C0Seq) →
    Filter.Tendsto (fun n ↦ C0Seq.pairingL x (c n)) Filter.atTop (𝓝 0))
