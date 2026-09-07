module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex

public section

/- Lemma 6.4b (Simultaneous choice of left vertices) -/
#check (Lorentz.leftVertex_spec :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (z₀ : Lorentz.parametrizedSubspace d) (k : ℕ),
    Lorentz.positiveCoordinate d hd (Lorentz.leftVertex d hd h_missing z₀ k) =
        Lorentz.leftTime k ∧
      (Lorentz.leftVertex d hd h_missing z₀ k : C0Seq × L1Seq).1 ∈
          C0Seq.remoteBall ∧
      ‖Lorentz.negativeCoordinate d hd (Lorentz.leftVertex d hd h_missing z₀ k) -
          Lorentz.leftTemplate (Lorentz.negativeCoordinate d hd z₀) (Lorentz.leftTime k)‖ <
        Lorentz.leftRadius k)
