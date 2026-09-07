module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing.RemoteSupport

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
