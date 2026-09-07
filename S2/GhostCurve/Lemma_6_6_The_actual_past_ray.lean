module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay

public section

/- Lemma 6.6 (The actual past ray) (1): the point `m(P)` on the ray belongs to
`Lorentz.parametrizedSubspace d`. -/
#check (Lorentz.pastRay :
  ∀ (d : C0Seq),
    Lorentz.parametrizedSubspace d → ℝ → Lorentz.parametrizedSubspace d)

/- Lemma 6.6 (The actual past ray) (2): the ray is defined by
`m(P) = (-P) • zLeft`. -/
#check (Lorentz.pastRay_apply :
  ∀ (d : C0Seq) (zLeft : Lorentz.parametrizedSubspace d) (P : ℝ),
    Lorentz.pastRay d zLeft P = (-P) • zLeft)

/- Lemma 6.6 (The actual past ray) (3): for `P ≤ -1`, the positive coordinate
of the ray point is `P`. -/
#check (Lorentz.positiveCoordinate_pastRay :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd zLeft = -1 →
      ∀ (P : ℝ), P ≤ -1 →
        Lorentz.positiveCoordinate d hd (Lorentz.pastRay d zLeft P) = P)

/- Lemma 6.6 (The actual past ray) (4): the left-anchor slope is strictly less
than `1`. -/
#check (Lorentz.pastRay_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < 1)

/- Lemma 6.6 (The actual past ray) (5): for `P ≤ -1`, the quadratic pairing
of the ray point is nonnegative. -/
#check (Lorentz.pastRay_quadraticPairing_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd zLeft = -1 →
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
        ∀ (P : ℝ), P ≤ -1 →
          0 ≤ C0Seq.quadraticPairing (Lorentz.pastRay d zLeft P))

/- Lemma 6.6 (The actual past ray) (6): for `P ≤ -1`, the negative-coordinate
norm scales by `-P`. -/
#check (Lorentz.pastRay_negativeCoordinate_norm :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d)
    (P : ℝ), P ≤ -1 →
      ‖Lorentz.negativeCoordinate d hd (Lorentz.pastRay d zLeft P)‖ =
        (-P) * ‖Lorentz.negativeCoordinate d hd zLeft‖)

/- Lemma 6.6 (The actual past ray) (7): for `P ≤ -1`, the negative-coordinate
norm satisfies `‖N(m(P))‖ < -P < 1 - P`. -/
#check (Lorentz.pastRay_negativeCoordinate_bounds :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
      ∀ (P : ℝ), P ≤ -1 →
        ‖Lorentz.negativeCoordinate d hd (Lorentz.pastRay d zLeft P)‖ < -P ∧
          -P < 1 - P)
