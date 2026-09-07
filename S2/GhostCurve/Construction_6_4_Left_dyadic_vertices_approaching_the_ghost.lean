module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex

/- Construction 6.4 (Left dyadic vertices approaching the ghost) -/
#check (Lorentz.leftVertex_spec :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : Lorentz.parametrizedSubspace d) (k : ℕ),
    Lorentz.positiveCoordinate d hd (Lorentz.leftVertex d hd h_missing z₀ k) =
        Lorentz.leftTime k ∧
      (Lorentz.leftVertex d hd h_missing z₀ k : C0Seq × L1Seq).1 ∈ C0Seq.remoteBall ∧
      ‖Lorentz.negativeCoordinate d hd (Lorentz.leftVertex d hd h_missing z₀ k) -
          Lorentz.leftTemplate (Lorentz.negativeCoordinate d hd z₀) (Lorentz.leftTime k)‖ <
        Lorentz.leftRadius k)

#check (Lorentz.leftTime_def :
  ∀ k : ℕ, Lorentz.leftTime k = 1 - (2 : ℝ) ^ (-(k + 1 : ℝ)))

#check (Lorentz.leftRadius_def :
  ∀ k : ℕ, Lorentz.leftRadius k = (2 : ℝ) ^ (-(k + 5 : ℝ)))
