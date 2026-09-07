module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Continuity
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Realization
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.Axis

public section

namespace Lorentz

variable (d : C0Seq) (hd : d ≠ 0)

/- Theorem 6.18 (Construction of the global ghost curve) (1): the assembled
negative-coordinate curve is continuous. -/
#check (Lorentz.continuous_ghostCurveN :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d),
    Continuous (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v))

/- Theorem 6.18 (Construction of the global ghost curve) (2): at ghost time
`1`, the assembled negative-coordinate curve has value `0`. -/
#check (Lorentz.ghostCurveN_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d),
    ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v 1 = 0)

/- Theorem 6.18 (Construction of the global ghost curve) (3): every time
other than ghost time is realized by a unique point of `parametrizedSubspace d`
with the prescribed positive and negative Lorentz coordinates. -/
#check (Lorentz.existsUnique_ghostCurveN_preimage :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (P : ℝ) (_ : P ≠ 1),
    ∃! z : parametrizedSubspace d,
      positiveCoordinate d hd z = P ∧
        negativeCoordinate d hd z =
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P)

/- Theorem 6.18 (Construction of the global ghost curve) (4): no point of
`parametrizedSubspace d` has Lorentz coordinates `(1, 0)`. -/
#check (Lorentz.axis_not_mem_embeddingRange d hd 1 one_ne_zero :
  (1, 0) ∉ Lorentz.embeddingRange d hd)

-- Range membership is the reusable existence input for the next source item.
#check (Lorentz.ghostCurveN_mem_embeddingRange :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (P : ℝ) (_ : P ≠ 1),
    (P, ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P) ∈
      embeddingRange d hd)

end Lorentz
