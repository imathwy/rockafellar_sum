module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Lipschitz

public section

namespace Lorentz

/- Lemma 6.20 (Global $1$-Lipschitz property and cone bounds) (1): the global
negative-coordinate curve is `1`-Lipschitz. -/
#check (Lorentz.lipschitzWith_ghostCurveN :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16),
    LipschitzWith 1 (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v))

/- Lemma 6.20 (Global $1$-Lipschitz property and cone bounds) (2): before the
ghost time, the norm of the negative-coordinate curve is bounded by `1 - P`. -/
#check (Lorentz.ghostCurveN_norm_le_one_sub :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (P : ℝ) (_ : P < 1),
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤ 1 - P)

/- Lemma 6.20 (Global $1$-Lipschitz property and cone bounds) (3): after the
ghost time, the norm of the negative-coordinate curve is bounded by `P - 1`. -/
#check (Lorentz.ghostCurveN_norm_le_sub_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (_ : 1 < P),
    ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ≤ P - 1)

end Lorentz
