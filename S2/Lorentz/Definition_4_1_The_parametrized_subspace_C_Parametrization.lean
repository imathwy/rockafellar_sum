module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization

#check (Lorentz.parametrization :
  C0Seq → (L1Seq × ℝ) →L[ℝ] (C0Seq × L1Seq))

#check (Lorentz.parametrization_apply :
  ∀ (d : C0Seq) (a : L1Seq) (t : ℝ),
    Lorentz.parametrization d (a, t) =
      (-L1Seq.positiveOperator a + t • d, a))

#check (Lorentz.parametrizedSubspace :
  C0Seq → Submodule ℝ (C0Seq × L1Seq))

#check (Lorentz.mem_parametrizedSubspace :
  ∀ (d : C0Seq) (z : C0Seq × L1Seq),
    z ∈ Lorentz.parametrizedSubspace d ↔
      ∃ a : L1Seq, ∃ t : ℝ,
        z = (-L1Seq.positiveOperator a + t • d, a))
