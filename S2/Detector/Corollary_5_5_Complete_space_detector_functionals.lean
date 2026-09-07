module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector

@[expose] public section

/- Corollary 5.5 (Complete-space detector functionals) (1): the detector functional
evaluates as the pairing of `x + L1Seq.positiveOperator u` with
`L1Seq.twoDet d p q`. -/
#check (Lorentz.detectorFunctional_apply :
  ∀ (d : C0Seq) (p q : ℕ) (x : C0Seq) (u : L1Seq),
    Lorentz.detectorFunctional d p q (x, u) =
      C0Seq.pairingL (x + L1Seq.positiveOperator u) (L1Seq.twoDet d p q))

/- Corollary 5.5 (Complete-space detector functionals) (2): if `d` is nonzero,
every point outside `Lorentz.parametrizedSubspace d` has a nonzero reading under
some detector functional with ordered coordinate indices. -/
#check (Lorentz.exists_detectorFunctional_ne_zero :
  ∀ (d : C0Seq) (w : C0Seq × L1Seq), d ≠ 0 →
    w ∉ Lorentz.parametrizedSubspace d →
      ∃ p q : ℕ, p < q ∧ Lorentz.detectorFunctional d p q w ≠ 0)
