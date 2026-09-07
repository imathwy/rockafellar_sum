module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.PastRay

public section

/- The concrete past-ray point is provided by the shared Lorentz API. -/
#check (Lorentz.pastRay :
  ∀ (d : C0Seq),
    Lorentz.parametrizedSubspace d → ℝ → Lorentz.parametrizedSubspace d)

/- The shared past-ray point has the prescribed scalar-multiple computation rule. -/
#check (Lorentz.pastRay_apply :
  ∀ (d : C0Seq) (zLeft : Lorentz.parametrizedSubspace d) (P : ℝ),
    Lorentz.pastRay d zLeft P = (-P) • zLeft)

/- The shared positive-coordinate computation identifies the ray parameter. -/
#check (Lorentz.positiveCoordinate_pastRay :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd zLeft = -1 →
      ∀ (P : ℝ), P ≤ -1 →
        Lorentz.positiveCoordinate d hd (Lorentz.pastRay d zLeft P) = P)

/- The shared negative-coordinate computation commutes with the ray scaling. -/
#check (Lorentz.negativeCoordinate_pastRay :
  ∀ (d : C0Seq) (hd : d ≠ 0) (zLeft : Lorentz.parametrizedSubspace d) (P : ℝ),
    Lorentz.negativeCoordinate d hd (Lorentz.pastRay d zLeft P) =
      (-P) • Lorentz.negativeCoordinate d hd zLeft)
