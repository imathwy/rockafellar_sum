module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Operator

public section

#check (Lorentz.ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (zLeft z₀ : Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (v : Lorentz.parametrizedSubspace d),
    SetValuedOperator C0Seq L1Seq)

#check (Lorentz.mem_ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (zLeft z₀ : Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (v : Lorentz.parametrizedSubspace d) (x : C0Seq) (xstar : L1Seq),
    xstar ∈ Lorentz.ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v x ↔
      (x, xstar) ∈ Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v)

#check (Lorentz.graph_ghostCurveOperator :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (zLeft z₀ : Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (h_tendsto : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (v : Lorentz.parametrizedSubspace d),
    (Lorentz.ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph =
      Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v)
