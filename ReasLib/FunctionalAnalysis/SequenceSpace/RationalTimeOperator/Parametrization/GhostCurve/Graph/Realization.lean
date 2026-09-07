module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Realization

public section

namespace Lorentz

/-- Every non-ghost time is the positive coordinate of a unique point of
`ghostGraph`, under the hypotheses constructing the global ghost curve. -/
theorem existsUnique_mem_ghostGraph
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (hvP : positiveCoordinate d hd v = 1)
    (P : ℝ) (hP : P ≠ 1) :
    ∃! z : parametrizedSubspace d,
      z.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v ∧
        positiveCoordinate d hd z = P := by
  have hpre := existsUnique_ghostCurveN_preimage d hd h_missing zLeft z₀
    hPLeft hPZero h h_positive h_tendsto v hvP P hP
  rcases hpre with ⟨z, hz, hzu⟩
  refine ⟨z, ?_, ?_⟩
  · change z.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v ∧
      positiveCoordinate d hd z = P
    apply And.intro
    · apply (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v z).2
      constructor
      · simpa [hz.1] using hP
      · simpa [hz.1] using hz.2
    · exact hz.1
  · intro y hy
    change y.val ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v ∧
      positiveCoordinate d hd y = P at hy
    have hy' := (mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v y).mp hy.1
    exact hzu y ⟨hy.2, by simpa [hy.2] using hy'.2⟩

/-- Twice a normalized future-ray base point belongs to the graph of the
assembled ghost curve. -/
theorem two_smul_mem_ghostGraph
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1) :
    ((2 : ℝ) • v).1 ∈ ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
  rw [mem_ghostGraph]
  constructor
  · have hcoord : positiveCoordinate d hd ((2 : ℝ) • v) = 2 := by
      rw [map_smul, hvP]
      norm_num
    rw [hcoord]
    norm_num
  · have hcoord : positiveCoordinate d hd ((2 : ℝ) • v) = 2 := by
      rw [map_smul, hvP]
      norm_num
    rw [hcoord]
    rw [ghostCurveN_of_two_le d hd h_missing zLeft z₀ h h_tendsto v 2 (by norm_num)]
    exact (negativeCoordinate d hd).map_smul 2 v

/-- The primal coordinate of twice a normalized future-ray base point belongs
to the domain of the assembled ghost-curve relation. -/
theorem two_smul_primal_mem_ghostGraph_dom
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1) :
    ((2 : ℝ) • v).1.1 ∈
      SetRel.dom (ghostGraph d hd h_missing zLeft z₀ h h_tendsto v) := by
  exact ⟨((2 : ℝ) • v).1.2,
    two_smul_mem_ghostGraph d hd h_missing zLeft z₀ h h_tendsto v hvP⟩

end Lorentz
