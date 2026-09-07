module

public import ReasLib.MeasureTheory.Measure.Lebesgue.Conull

/- Lemma 2.7c (Two-sided conull points avoiding finitely many breakpoints) -/
#check (Real.exists_conull_points_around_avoiding_finset :
  ∀ {E : Set ℝ},
    E ⊆ Set.Ioo (0 : ℝ) 1 →
    MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 \ E) = 0 →
    ∀ {t : ℝ}, t ∈ Set.Ioo 0 1 →
    ∀ (F : Finset ℝ), t ∉ F →
    ∀ (ε : ℝ), 0 < ε →
      ∃ sLeft ∈ E ∩ Set.Ioo (t - ε) t,
        ∃ sRight ∈ E ∩ Set.Ioo t (t + ε),
          ∀ x ∈ F, x ∉ Set.Ioo sLeft sRight)
