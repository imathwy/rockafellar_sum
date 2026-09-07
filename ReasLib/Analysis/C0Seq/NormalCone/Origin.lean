module

public import ReasLib.Analysis.C0Seq.NormalCone
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing.Origin

public section

open scoped Pointwise

namespace C0Seq

/-- A monotone operator graph containing a point with negative quadratic pairing
does not contain the origin after adding the normal cone of `finalConstraint`. -/
theorem zero_not_mem_add_normalCone_graph_of_quadraticPairing_neg
    (M : SetValuedOperator C0Seq L1Seq) (z : C0Seq × L1Seq)
    (hz : z ∈ M.graph) (hz_neg : quadraticPairing z < 0)
    (hM : coordinateDualPairing.IsMonotone M.graph) :
    (0, 0) ∉ (M + coordinateDualPairing.normalCone finalConstraint).graph := by
  intro hzero
  have hMzero : (0, 0) ∈ M.graph :=
    zero_mem_graph_of_mem_add_normalCone coordinateDualPairing M hzero
  exact zero_not_mem_of_quadraticPairing_neg hz hz_neg hM hMzero

end C0Seq
