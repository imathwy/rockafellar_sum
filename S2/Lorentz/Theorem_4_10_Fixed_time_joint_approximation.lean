/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import S2.Lorentz.fix_P_coordinate

/-!
# Fixed-time joint approximation

This module exposes the simultaneous approximation theorem for prescribed
Lorentz coordinates.
-/

/- Theorem 4.10 (Fixed-time joint approximation): for prescribed `p`, `x₀`,
`v`, `r`, and positive `ε`, one point of `Lorentz.parametrizedSubspace d` has
positive coordinate exactly `p` while its first ambient coordinate and negative
coordinate approximate `x₀` and `HilbertProd2.mk v r` within `ε`. -/
#check Lorentz.exists_approx_fixedPositiveCoordinate
