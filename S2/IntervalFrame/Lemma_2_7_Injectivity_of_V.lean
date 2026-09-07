module

public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Injective

/- Lemma 2.7 (Injectivity of $V$). The interval-coordinate operator has trivial kernel:
if `L1Seq.intervalCoordinateOperator a = 0`, then `a = 0`. -/
#check (L1Seq.intervalCoordinateOperator_injective :
  Function.Injective L1Seq.intervalCoordinateOperator)
