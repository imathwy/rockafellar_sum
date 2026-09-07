module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Relocation

@[expose] public section

noncomputable section

/- Lemma 2.12 (Remote replication of finitely supported coefficients).
Every finitely supported coefficient vector has an equal-norm copy supported beyond any
prescribed cutoff whose interval-coordinate synthesis is arbitrarily close to the original. -/
#check (L1Seq.exists_remoteReplication :
  ∀ (b : L1Seq) (_ : (fun i ↦ b i).HasFiniteSupport)
      (N : ℕ) (ε : ℝ), 0 < ε →
    ∃ b' : L1Seq,
      Function.support (fun n ↦ b' n) ⊆ Set.Ioi N ∧
        ‖b'‖ = ‖b‖ ∧
        ‖L1Seq.intervalCoordinateOperator b' - L1Seq.intervalCoordinateOperator b‖ < ε)
