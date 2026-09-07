module

public import Mathlib.Topology.Maps.Basic

public section

open Filter
open scoped Topology

universe u v w

namespace Topology.IsClosedEmbedding

/-- A convergent net mapped through a closed embedding has a unique preimage to which
the original net converges. -/
theorem existsUnique_tendsto {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) {ι : Type w} (g : ι → X)
    (l : Filter ι) [NeBot l] (y : Y) (h : Tendsto (f ∘ g) l (𝓝 y)) :
    ∃! x : X, Tendsto g l (𝓝 x) ∧ y = f x := by
  -- The mapped net remains in the closed range of the embedding.
  have h_range : ∀ᶠ i in l, (f ∘ g) i ∈ Set.range f :=
    Eventually.of_forall fun i ↦ Set.mem_range_self (g i)
  -- Closedness therefore supplies a preimage of the ambient limit.
  have hy : y ∈ Set.range f := hf.isClosed_range.mem_of_tendsto h h_range
  rcases hy with ⟨x, rfl⟩
  -- The inducing part of the embedding reflects convergence to that preimage.
  have hg : Tendsto g l (𝓝 x) := hf.tendsto_nhds_iff.mpr h
  refine ⟨x, ⟨hg, rfl⟩, ?_⟩
  intro x' hx'
  -- Injectivity makes this preimage, and hence the recovered limit, unique.
  exact hf.injective hx'.2.symm

end Topology.IsClosedEmbedding
