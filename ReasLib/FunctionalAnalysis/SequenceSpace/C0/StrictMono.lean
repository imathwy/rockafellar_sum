/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0

/-!
# Strictly increasing samples of `c₀` sequences
-/

public section

open Topology

namespace C0Seq

/-- Coordinates of a `c₀` sequence vanish along every strictly increasing
subsequence of indices. -/
theorem tendsto_apply_strictMono (x : C0Seq) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) :
    Filter.Tendsto (fun n ↦ x (φ n)) Filter.atTop (𝓝 0) := by
  exact (tendsto_zero x).comp hφ.tendsto_atTop

end C0Seq
