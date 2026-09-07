module

public import S2.Lorentz.fix_P_coordinate

/- Theorem 4.10 (Fixed-time joint approximation): for prescribed `p`, `x₀`,
`v`, `r`, and positive `ε`, one point of `Lorentz.parametrizedSubspace d` has
positive coordinate exactly `p` while its first ambient coordinate and negative
coordinate approximate `x₀` and `HilbertProd2.mk v r` within `ε`. -/
#check Lorentz.exists_approx_fixedPositiveCoordinate
