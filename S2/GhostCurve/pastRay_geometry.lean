module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay

public section

/- A normalized scalar multiple has its displayed coordinates in the range of
the Lorentz embedding. -/
#check (Lorentz.pastRay_mem_embeddingRange :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd zLeft = -1 → ∀ P : ℝ,
      (P, Lorentz.negativeCoordinate d hd ((-P) • zLeft)) ∈
        Lorentz.embeddingRange d hd)

/- Lemma 6.6a (Past-ray energy and cone inequalities) (1): the normalized
left anchor has slope strictly less than `1`. -/
#check (Lorentz.pastRay_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < 1)

/- At a scale `P ≤ -1`, the negative-coordinate norm is multiplied by `-P`. -/
#check (Lorentz.pastRay_negativeCoordinate_norm :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d)
    (P : ℝ), P ≤ -1 →
      ‖Lorentz.negativeCoordinate d hd ((-P) • zLeft)‖ =
        (-P) * ‖Lorentz.negativeCoordinate d hd zLeft‖)

/- Lemma 6.6a (Past-ray energy and cone inequalities) (2): for `P ≤ -1`,
the explicit point `(-P) • zLeft` satisfies the strict norm chain. -/
#check (Lorentz.pastRay_negativeCoordinate_bounds :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
      ∀ (P : ℝ), P ≤ -1 →
        ‖Lorentz.negativeCoordinate d hd ((-P) • zLeft)‖ < -P ∧
          -P < 1 - P)

/- The embedded normalized past-ray point belongs to the past Lorentz cone. -/
#check (Lorentz.pastRay_mem_pastCone :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd zLeft = -1 →
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
        ∀ (P : ℝ), P ≤ -1 →
          Lorentz.embedding d hd ((-P) • zLeft) ∈
            Lorentz.pastCone (HilbertProd2 UnitL2))

/- The embedded normalized past-ray point has nonnegative Lorentz energy. -/
#check (Lorentz.pastRay_energy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd zLeft = -1 →
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
        ∀ (P : ℝ), P ≤ -1 →
          0 ≤ Lorentz.energy (Lorentz.embedding d hd ((-P) • zLeft)))

/- Lemma 6.6a (Past-ray energy and cone inequalities) (3): for `P ≤ -1`,
the explicit point `(-P) • zLeft` has nonnegative quadratic pairing. -/
#check (Lorentz.pastRay_quadraticPairing_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd zLeft = -1 →
      ‖Lorentz.negativeCoordinate d hd zLeft‖ < (1 : ℝ) / 16 →
        ∀ (P : ℝ), P ≤ -1 →
          0 ≤ C0Seq.quadraticPairing ((-P) • zLeft))
