/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Normed.Group.Sequences
public import S2.Infra.HilbertProd2
public import S2.Infra.UnitL2_Space

/-!
# Ghost-Time Polar Limit

This module exposes the limiting polar inequality at the missing ghost time.
-/

public section

open scoped Topology

namespace Lorentz

/- Lemma 7.5a (Limit inequality at the missing time): if non-ghost times `P k`
converge to `1`, the polar inequalities and continuity of `f` at `1` with
`f 1 = 0` force the fixed comparison point `N` to vanish. -/
#check (eq_zero_of_tendsto_sq_norm_bound (E := HilbertProd2 UnitL2) (a := 1) :
  ∀ (f : ℝ → HilbertProd2 UnitL2) (N : HilbertProd2 UnitL2) (P : ℕ → ℝ),
    ContinuousAt f 1 → f 1 = 0 → Filter.Tendsto P Filter.atTop (𝓝 1) →
    (∀ k, P k ≠ 1) →
    (∀ k, P k ≠ 1 → 0 ≤ (1 - P k) ^ 2 - ‖N - f (P k)‖ ^ 2) →
    N = 0)

end Lorentz
