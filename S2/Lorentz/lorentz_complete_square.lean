module

public import ReasLib.Analysis.Normed.LorentzCone.HilbertProd2
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator

public section

variable (d : C0Seq) (a : L1Seq) (t : ℝ)

/- Lemma 4.4a (Algebraic completion of the square): the quadratic expression in
the interval coordinates is the stated difference of squares. -/
#check (Lorentz.completeSquare (L1Seq.intervalCoordinateOperator a)
  (C0Seq.pairingL d a) t :
    -(‖L1Seq.intervalCoordinateOperator a‖ ^ 2) + t * C0Seq.pairingL d a =
      ((t + C0Seq.pairingL d a) / 2) ^ 2 -
        (‖L1Seq.intervalCoordinateOperator a‖ ^ 2 +
          ((t - C0Seq.pairingL d a) / 2) ^ 2))

/- The same specialization identifies the completed square with Lorentz energy. -/
#check (Lorentz.completeSquareEnergy (L1Seq.intervalCoordinateOperator a)
  (C0Seq.pairingL d a) t :
    -(‖L1Seq.intervalCoordinateOperator a‖ ^ 2) + t * C0Seq.pairingL d a =
      Lorentz.energy
        ((t + C0Seq.pairingL d a) / 2,
          HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
            ((t - C0Seq.pairingL d a) / 2)))
