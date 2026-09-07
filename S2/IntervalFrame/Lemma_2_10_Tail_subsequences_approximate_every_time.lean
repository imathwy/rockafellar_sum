module

public import ReasLib.Topology.RationalTime

open Topology

/- Lemma 2.10 (Tail subsequences approximate every time). For every
`t ∈ Set.Icc (0 : ℝ) 1`, the sequence `rationalTime` has a strictly increasing
subsequence converging to `t`. -/
#check (exists_strictMono_rationalTime_tendsto :
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (rationalTime ∘ φ) Filter.atTop (𝓝 t))
