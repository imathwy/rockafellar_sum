module

public import ReasLib.Topology.Maps.ClosedEmbedding
public import Mathlib.Topology.Algebra.Module.FiniteDimension

public section

open Filter
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (d : E) (hd : d ≠ 0)

/- Infrastructure C.4 (Closedness and scalar recovery for a nonzero one-dimensional range) (1):
the range of scalar multiplication by a nonzero vector is closed. -/
#check ((isClosedEmbedding_smul_left hd).isClosed_range :
  IsClosed (Set.range (fun s : ℝ ↦ s • d)))

variable (t : ℕ → ℝ) (x : E)
variable (h : Tendsto (fun n ↦ t n • d) atTop (𝓝 x))

/- Infrastructure C.4 (Closedness and scalar recovery for a nonzero one-dimensional range) (2):
convergence of scalar multiples of a nonzero vector uniquely determines the scalar limit. -/
#check (Topology.IsClosedEmbedding.existsUnique_tendsto
    (isClosedEmbedding_smul_left hd) t atTop x h :
  ∃! s : ℝ, Tendsto t atTop (𝓝 s) ∧ x = s • d)
