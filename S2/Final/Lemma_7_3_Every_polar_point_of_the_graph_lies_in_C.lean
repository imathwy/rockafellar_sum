/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Polar

/-!
# Polar points lie in the parametrized subspace

This module records the subspace reduction for polar points of the ghost-curve graph.
-/

public section

namespace Lorentz

/- Lemma 7.3 (Every polar point of the graph lies in $C$)
-/
#check (Lorentz.mem_parametrizedSubspace_of_mem_ghostCurveOperator_polar :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (w : C0Seq × L1Seq)
    (_ : w ∈ C0Seq.monotonePolar
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph)
    (_ : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w))),
    w ∈ parametrizedSubspace d)

end Lorentz
