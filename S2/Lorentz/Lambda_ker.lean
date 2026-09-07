module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.Kernel

public section

namespace Lorentz

/-- Lemma 4.6a (Zero Lorentz coordinates force the zero parameter). If both
Lorentz coordinates of `parametrizedPoint d a t` vanish, then `a = 0` and
`t = 0`. -/
theorem lambda_ker (d : C0Seq) (hd : d ≠ 0) (a : L1Seq) (t : ℝ)
    (hP : positiveCoordinate d hd (parametrizedPoint d a t) = 0)
    (hN : negativeCoordinate d hd (parametrizedPoint d a t) = 0) :
    a = 0 ∧ t = 0 :=
  parameters_eq_zero_of_negativeCoordinate_eq_zero d hd a t hN

end Lorentz
