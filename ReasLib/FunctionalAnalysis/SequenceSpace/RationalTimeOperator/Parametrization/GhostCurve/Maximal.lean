module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Monotone
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Polar
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Polar.Rigidity

public section

namespace Lorentz

/-- The monotone polar of a ghost-curve operator graph is the graph itself. -/
theorem monotonePolar_ghostCurveOperator_graph
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hvP : positiveCoordinate d hd v = 1)
    (h_zLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (h_anchor : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (h_z₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (h_v : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (h_pairing : ∀ (w : C0Seq × L1Seq) p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w))) :
    C0Seq.monotonePolar
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph =
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph := by
  apply Set.Subset.antisymm
  · intro w hw
    have hw_sub : w ∈ parametrizedSubspace d :=
      mem_parametrizedSubspace_of_mem_ghostCurveOperator_polar
        d hd h_missing zLeft z₀ h h_positive h_tendsto v w hw (h_pairing w)
    let wz : parametrizedSubspace d := ⟨w, hw_sub⟩
    have hw_ne : positiveCoordinate d hd wz ≠ 1 :=
      positiveCoordinate_ne_one_of_mem_ghostCurveOperator_polar
        d hd h_missing zLeft z₀ h h_positive h_tendsto v
        h_zLeft h_anchor h_z₀ h_v wz hw
    have hw_graph : wz.val ∈
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph :=
      mem_ghostCurveOperator_of_polar_ne_one
        d hd h_missing zLeft z₀ h h_tendsto v
        hPLeft hPZero h_positive hvP wz hw hw_ne
    simpa [wz] using hw_graph
  · have hmono :=
      isMonotone_ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v
        h_zLeft h_anchor h_z₀ h_v
    have hsub :=
      (DualPairing.isMonotone_iff_subset_polar
        C0Seq.coordinateDualPairing
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph).mp hmono
    rw [C0Seq.monotonePolar_eq_coordinateDualPairing]
    exact hsub

/-- A ghost-curve operator graph is maximal among monotone subsets of
`C0Seq × L1Seq`. -/
theorem maximalMonotone_ghostCurveOperator
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d)
    (hPLeft : positiveCoordinate d hd zLeft = -1)
    (hPZero : positiveCoordinate d hd z₀ = 0)
    (hvP : positiveCoordinate d hd v = 1)
    (h_zLeft : ‖negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16)
    (h_anchor : ‖negativeCoordinate d hd zLeft - negativeCoordinate d hd z₀‖ < 1)
    (h_z₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (h_v : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (h_pairing : ∀ (w : C0Seq × L1Seq) p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w))) :
    Maximal C0Seq.coordinateDualPairing.IsMonotone
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph := by
  have hmono :=
    isMonotone_ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v
      h_zLeft h_anchor h_z₀ h_v
  have heq :=
    monotonePolar_ghostCurveOperator_graph d hd h_missing zLeft z₀ h
      h_positive h_tendsto v hPLeft hPZero hvP h_zLeft h_anchor h_z₀ h_v h_pairing
  have heq' :
      C0Seq.coordinateDualPairing.monotonePolar
          (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph =
        (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph := by
    calc
      C0Seq.coordinateDualPairing.monotonePolar
          (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph =
          C0Seq.monotonePolar
            (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph :=
        (C0Seq.monotonePolar_eq_coordinateDualPairing _).symm
      _ = _ := heq
  exact
    (DualPairing.maximalMonotone_iff_polar_eq
      C0Seq.coordinateDualPairing
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph hmono).2 heq'

end Lorentz
