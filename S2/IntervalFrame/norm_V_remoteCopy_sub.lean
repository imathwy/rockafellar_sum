module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Relocation

@[expose] public section

noncomputable section

namespace L1Seq

/- The coefficient-weighted displacement estimate for interval-coordinate synthesis. -/
#check (norm_intervalCoordinateOperator_remoteCopy_sub_le :
    ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport) (m : ℕ → ℕ),
    ‖intervalCoordinateOperator (remoteCopy b h_b m) - intervalCoordinateOperator b‖ ≤
      ∑ i ∈ h_b.toFinset,
        |b i| * Real.sqrt |rationalTime (m i) - rationalTime i|)

/- Lemma 2.12c (Synthesis error of a remote copy).
Every finitely supported coefficient vector admits an injective relocation beyond `N`
whose interval-coordinate synthesis error is less than any prescribed positive `ε`. -/
#check (exists_remoteCopy_synthesisError_lt :
    ∀ (b : L1Seq) (h_b : (fun i ↦ b i).HasFiniteSupport)
      (N : ℕ) (ε : ℝ) (_hε : 0 < ε),
    ∃ m : ℕ → ℕ,
      (Set.InjOn m (Function.support fun i ↦ b i) ∧
        ∀ i, b i ≠ 0 → N < m i) ∧
      ‖intervalCoordinateOperator (remoteCopy b h_b m) - intervalCoordinateOperator b‖ <
        ε)

end L1Seq
