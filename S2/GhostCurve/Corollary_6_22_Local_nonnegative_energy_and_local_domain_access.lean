module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph.Realization
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Localization
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Realization
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay

public section

namespace Lorentz

/- Corollary 6.22 (Local nonnegative energy and local domain access) (1):
the quadratic pairing of a point realized on `ghostCurveN` equals its Lorentz
energy. -/
#check (Lorentz.ghostCurveN_quadraticPairing_eq :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (P : ℝ) (m : parametrizedSubspace d)
    (_ :
      (P, ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P) = embedding d hd m),
    C0Seq.quadraticPairing m =
      P ^ 2 - ‖ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P‖ ^ 2)

/- Corollary 6.22 (Local nonnegative energy and local domain access) (2):
a point realized on `ghostCurveN` with primal coordinate in
`C0Seq.localOpenUnitBall` has nonnegative quadratic pairing. -/
#check (Lorentz.ghostCurveN_localEnergy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (_ : positiveCoordinate d hd zLeft = -1)
    (_ : positiveCoordinate d hd z₀ = 0)
    (_ : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (_ : ‖negativeCoordinate d hd z₀‖ < (1 : ℝ) / 32)
    (_ : zLeft.1.1 ∈ C0Seq.remoteBall)
    (_ : z₀.1.1 ∈ C0Seq.remoteBall)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1)
    (_ : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (m : parametrizedSubspace d)
    (_ :
      (P, ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v P) = embedding d hd m)
    (_ : m.1.1 ∈ C0Seq.localOpenUnitBall),
    0 ≤ C0Seq.quadraticPairing m)

/- Corollary 6.22 (Local nonnegative energy and local domain access) (3):
the concrete point `(2 : ℝ) • v` belongs to the actual ghost curve. -/
#check (Lorentz.two_smul_mem_ghostGraph :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1),
    ((2 : ℝ) • v).1 ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v)

/- Corollary 6.22 (Local nonnegative energy and local domain access) (4):
the primal coordinate of `(2 : ℝ) • v` belongs to the domain of the actual
ghost curve relation. -/
#check (Lorentz.two_smul_primal_mem_ghostGraph_dom :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (_ : positiveCoordinate d hd v = 1),
    ((2 : ℝ) • v).1.1 ∈
      SetRel.dom (ghostGraph d hd h_missing zLeft z₀ h h_tendsto v))

/- Corollary 6.22 (Local nonnegative energy and local domain access) (5):
the primal coordinate of `(2 : ℝ) • v` has norm less than `1 / 4` when the
primal coordinate of `v` has norm less than `1 / 8`. -/
#check (Lorentz.norm_two_smul_primal_lt_quarter :
  ∀ (d : C0Seq) (v : parametrizedSubspace d)
    (_ : ‖v.1.1‖ < (1 : ℝ) / 8),
    ‖((2 : ℝ) • v).1.1‖ < (1 : ℝ) / 4)

end Lorentz
