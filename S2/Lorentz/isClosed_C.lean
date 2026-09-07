module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.ClosedRange

public section

/-
Lemma 4.2c (Closedness of the parametrized range): if `d ≠ 0`, then the
subspace parametrized by `Ψ(a, t) = (-Aa + t • d, a)` is closed.
-/
#check (Lorentz.isClosed_parametrizedSubspace : ∀ (d : C0Seq), d ≠ 0 →
  IsClosed (Lorentz.parametrizedSubspace d : Set (C0Seq × L1Seq)))
