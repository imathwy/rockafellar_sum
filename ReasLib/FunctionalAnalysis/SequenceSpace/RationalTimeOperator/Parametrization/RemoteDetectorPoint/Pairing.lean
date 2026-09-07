module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Pairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPoint

public section

open scoped InnerProductSpace

namespace Lorentz

/-- The symmetric pairing with a remote detector point expands into the
positive-operator pairing, the interval-coordinate inner product, and the
product of the pairings against the parametrizing sequence. -/
theorem symmetricForm_remoteDetectorPoint
    (d x : C0Seq) (u : L1Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    let a := L1Seq.remoteDetectorDifference d p q c n
    C0Seq.symmetricForm (x, u) (remoteDetectorPoint d p q c n) =
      C0Seq.pairingL (x + L1Seq.positiveOperator u) a -
        2 * ⟪L1Seq.intervalCoordinateOperator u,
          L1Seq.intervalCoordinateOperator a⟫_ℝ -
        C0Seq.pairingL d u * C0Seq.pairingL d a := by
  -- Expose the ambient parametrization represented by the remote detector point.
  rw [remoteDetectorPoint_apply, parametrizedPoint_apply]
  -- Specialize the general detector-pairing identity to the remote difference.
  exact detectorPairingFormula d x u (L1Seq.remoteDetectorDifference d p q c n)

end Lorentz
