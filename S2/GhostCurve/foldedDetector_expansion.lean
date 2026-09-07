module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Pairing

public section

namespace Lorentz

/- Lemma 6.14a (Exact expansion of B(w,m_i)-c(m_i)): the symmetric pairing
minus the quadratic pairing at the `i`-th folded right vertex separates into
the signed scaled detector reading and the base, cross, and perturbation terms. -/
#check (Lorentz.symmetricForm_rightVertex_sub_quadraticPairing :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (w : C0Seq × L1Seq) (i : ℕ),
    let ξ := nearGhostBase d hd h_missing i
    let δ := detectorPerturbation d hd h_missing h h_tendsto i
    let m := rightVertex d hd h_missing h h_tendsto i
    let hᵢ := scheduledDetectorPoint h i
      (detectorIndex d hd h_missing h h_tendsto i)
    C0Seq.symmetricForm w m - C0Seq.quadraticPairing m =
      (((DetectorTriple.schedule.toFun i).sign : ℝ) *
          detectorScale d hd h_missing i) * C0Seq.symmetricForm w hᵢ +
        C0Seq.symmetricForm w ξ - C0Seq.quadraticPairing ξ -
          C0Seq.symmetricForm ξ δ - C0Seq.quadraticPairing δ)

end Lorentz
