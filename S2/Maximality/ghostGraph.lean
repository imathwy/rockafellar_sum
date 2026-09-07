module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph.Realization

public section

namespace Lorentz

variable (d : C0Seq) (hd : d ≠ 0)
variable (h_missing : d ∉ Set.range L1Seq.positiveOperator)
variable (zLeft z₀ : parametrizedSubspace d)
variable (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
variable (h_tendsto : ∀ p q (h_pq : p < q),
  Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
    Filter.atTop (nhds 0))
variable (v : parametrizedSubspace d)

/- Definition 7.1a (Graph without a partial inverse of Λ): the ambient graph
consists of the points in `parametrizedSubspace d` whose positive coordinate is
not the ghost time and whose negative coordinate lies on `ghostCurveN`. -/
#check (Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v :
  Set (C0Seq × L1Seq))

#check (Lorentz.mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v :
  ∀ z : parametrizedSubspace d,
    z.val ∈ Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v ↔
      positiveCoordinate d hd z ≠ 1 ∧
        negativeCoordinate d hd z =
          ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v
            (positiveCoordinate d hd z))

#check (Lorentz.ghostGraph_eq_preimage_graphOn
  d hd h_missing zLeft z₀ h h_tendsto v :
    Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v =
      Subtype.val '' ((embedding d hd) ⁻¹'
        Set.graphOn (ghostCurveN d hd h_missing zLeft z₀ h h_tendsto v)
          {P : ℝ | P ≠ 1}))

#check (Lorentz.existsUnique_mem_ghostGraph
  d hd h_missing zLeft z₀ h h_tendsto v :
    positiveCoordinate d hd zLeft = -1 →
    positiveCoordinate d hd z₀ = 0 →
    (∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0) →
    positiveCoordinate d hd v = 1 →
    ∀ P : ℝ, P ≠ 1 →
      ∃! z : parametrizedSubspace d,
        z.val ∈ Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v ∧
          positiveCoordinate d hd z = P)

end Lorentz
