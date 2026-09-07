module

public import ReasLib.Topology.Sequences

public section

open Filter Topology

universe u

/- Infrastructure B.10 (Increasing tail subsequences from a tail-dense enumeration)
-/
#check (exists_strictMono_subseq_tendsto :
  ∀ {X : Type u} [MetricSpace X] (x : ℕ → X),
    (∀ b : X, ∀ U ∈ 𝓝 b, ∀ N : ℕ, ∃ n : ℕ, N < n ∧ x n ∈ U) →
    ∀ a : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a))
