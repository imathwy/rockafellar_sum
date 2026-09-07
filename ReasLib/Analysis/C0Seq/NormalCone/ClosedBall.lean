module

public import ReasLib.Analysis.C0Seq.NormalCone
public import ReasLib.Analysis.Convex.NormalCone.ClosedBall
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing.Surjective

public section

namespace C0Seq

/-- Every point monotonically compatible with the normal-cone graph of the closed
radius-`1 / 2` ball in real `c₀` belongs to that graph. -/
theorem finalConstraint_normalCone_polar_subset :
    coordinateDualPairing.monotonePolar
        (coordinateDualPairing.normalConeGraph finalConstraint) ⊆
      coordinateDualPairing.normalConeGraph finalConstraint := by
  have hmax :=
    DualPairing.maximalMonotone_normalConeGraph_closedBall
      coordinateDualPairing coordinateDualPairing_surjective (1 / 2) one_half_pos
  have hmono :=
    coordinateDualPairing.isMonotone_normalConeGraph finalConstraint
  have heq :=
    (coordinateDualPairing.maximalMonotone_iff_polar_eq
      (coordinateDualPairing.normalConeGraph finalConstraint) hmono).1 hmax
  rw [heq]

end C0Seq
