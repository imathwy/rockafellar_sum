module

public import ReasLib.Topology.MetricSpace.Lipschitz

universe u

/- Infrastructure E.6 (Cross-accumulation Lipschitz gluing): a map vanishing at `1`
that is `K`-Lipschitz on both closed half-lines and obeys the stated anchor bound is
globally `K`-Lipschitz. -/
#check (LipschitzWith.of_iic_ici_of_norm_le (1 : ℝ) :
  ∀ {E : Type u} [SeminormedAddGroup E] {K : NNReal} {f : ℝ → E},
    f 1 = 0 →
      LipschitzOnWith K f (Set.Iic 1) →
        LipschitzOnWith K f (Set.Ici 1) →
          (∀ P : ℝ, ‖f P‖ ≤ K * |P - 1|) → LipschitzWith K f)
