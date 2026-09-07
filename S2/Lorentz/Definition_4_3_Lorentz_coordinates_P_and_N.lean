module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates

/- Definition 4.3 (Lorentz coordinates $P$ and $N$) (1): the positive coordinate
`P(z) = (t + d(a)) / 2` for `z = Ψ(a, t)`. -/
#check (Lorentz.positiveCoordinate_apply :
  ∀ (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ),
    Lorentz.positiveCoordinate d hd (Lorentz.parametrizedPoint d a t) =
      (t + C0Seq.pairingL d a) / 2)

/- Definition 4.3 (Lorentz coordinates $P$ and $N$) (2): the negative coordinate
`N(z) = (V a, (t - d(a)) / 2)` for `z = Ψ(a, t)`. -/
#check (Lorentz.negativeCoordinate_apply :
  ∀ (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ),
    Lorentz.negativeCoordinate d hd (Lorentz.parametrizedPoint d a t) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        ((t - C0Seq.pairingL d a) / 2))
