module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph.RightVertex

public section

/- Lemma 7.3a (Polar compatibility bounds every detector vertex): if `w` lies
in the monotone polar of the ghost graph, then its pairing gap against every
folded right-hand detector vertex is bounded by `C0Seq.quadraticPairing w`. -/
#check (Lorentz.rightVertex_gap_le :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : Lorentz.parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : Lorentz.parametrizedSubspace d) (w : C0Seq × L1Seq)
    (_ : w ∈ C0Seq.monotonePolar
      (Lorentz.ghostGraph d hd h_missing zLeft z₀ h h_tendsto v)) (i : ℕ),
    C0Seq.symmetricForm w (Lorentz.rightVertex d hd h_missing h h_tendsto i) -
        C0Seq.quadraticPairing
          (Lorentz.rightVertex d hd h_missing h h_tendsto i) ≤
      C0Seq.quadraticPairing w)
