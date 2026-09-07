module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Injective

public section

/- Lemma 4.2a (Injectivity of the Ψ parametrization). If `d ≠ 0`, then the
parametrization `Ψ(a, t) = (-Aa + t • d, a)` is injective. -/
#check (Lorentz.parametrization_injective :
  ∀ (d : C0Seq), d ≠ 0 → Function.Injective (Lorentz.parametrization d))
