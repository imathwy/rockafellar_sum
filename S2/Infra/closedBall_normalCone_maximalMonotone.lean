/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Convex.NormalCone.ClosedBall

/-!
# Closed-Ball Normal Cones

This module exposes maximal-monotonicity criteria for closed-ball normal cones.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]
  [CompleteSpace Xstar]

variable (P : DualPairing X Xstar) (h_surjective : Function.Surjective P.toDual)
  (r : ℝ) (hr : 0 < r)

/- Infrastructure D.10 (Maximal monotonicity of a closed-ball normal cone) (1):
the normal-cone graph of a positive-radius closed ball is maximally monotone when
the pairing map onto the strong dual is surjective. -/
#check (DualPairing.maximalMonotone_normalConeGraph_closedBall P h_surjective r hr :
  Maximal P.IsMonotone (P.normalConeGraph (Metric.closedBall (0 : X) r)))

/- Infrastructure D.10 (Maximal monotonicity of a closed-ball normal cone) (2):
the domain of the closed-ball normal cone is exactly that closed ball. -/
#check (DualPairing.dom_normalCone P (Metric.closedBall (0 : X) r) :
  P.normalConeDom (Metric.closedBall (0 : X) r) = Metric.closedBall (0 : X) r)

end DualPairing
