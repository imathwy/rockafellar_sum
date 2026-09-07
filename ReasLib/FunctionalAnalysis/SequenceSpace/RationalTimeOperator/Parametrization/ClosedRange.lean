module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Convergence

public section

open Filter

namespace Lorentz

/-- The range of the rational-time parametrization in a nonzero direction is closed. -/
theorem isClosed_parametrizedSubspace (d : C0Seq) (hd : d ≠ 0) :
    IsClosed (parametrizedSubspace d : Set (C0Seq × L1Seq)) := by
  -- It suffices to reconstruct the parameters of the limit of any convergent sequence.
  apply IsSeqClosed.isClosed
  intro z p hz hzp
  classical
  -- Choose parameters representing every term of the sequence in the range.
  have hParameters : ∀ k, ∃ a : L1Seq, ∃ t : ℝ,
      z k = (-L1Seq.positiveOperator a + t • d, a) := by
    intro k
    exact (mem_parametrizedSubspace d (z k)).mp (hz k)
  choose aSeq tSeq hRepresentation using hParameters
  -- Normalize the represented sequence to the canonical parametrization.
  have hParametrized :
      (fun k ↦ parametrization d (aSeq k, tSeq k)) = z := by
    funext k
    rw [parametrization_apply]
    exact (hRepresentation k).symm
  have hParametrizedTendsto :
      Tendsto (fun k ↦ parametrization d (aSeq k, tSeq k)) atTop
        (nhds (p.1, p.2)) := by
    rw [hParametrized]
    simpa only [Prod.eta] using hzp
  -- Recover the limiting scalar and hence the required representation of the limit.
  obtain ⟨s, ⟨_, hReconstruction⟩, _⟩ :=
    existsUniqueLimitParameter d aSeq tSeq p.1 p.2 hd hParametrizedTendsto
  apply (mem_parametrizedSubspace d p).mpr
  refine ⟨p.2, s, ?_⟩
  apply Prod.ext
  · exact hReconstruction
  · rfl

end Lorentz
