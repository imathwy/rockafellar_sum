/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Topology.RationalTime

/-!
# Zero From Tail-Dense Samples

This module exposes the continuous extension from vanishing rational-time samples.
-/

open Topology

/- Lemma 2.11b (Tail-dense zero samples force a continuous primitive to vanish).
If `G` is continuous on `Set.Icc (0 : ℝ) 1` and its values along `rationalTime`
tend to zero, then `G` vanishes throughout that interval. -/
#check (continuousOn_eq_zero_of_tendsto_rationalTime :
  ∀ (G : ℝ → ℝ),
    ContinuousOn G (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun n : ℕ ↦ G (rationalTime n)) Filter.atTop (𝓝 0) →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, G t = 0)
