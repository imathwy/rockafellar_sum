module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPoint.Pairing

public section

open scoped InnerProductSpace

/-
Lemma 5.10 (Detector pairing identity): for a remote-detector difference `a`,
the symmetric pairing with its detector point has the stated expansion.
-/
#check (Lorentz.symmetricForm_remoteDetectorPoint :
  ∀ (d x : C0Seq) (u : L1Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    let a := L1Seq.remoteDetectorDifference d p q c n
    C0Seq.symmetricForm (x, u) (Lorentz.remoteDetectorPoint d p q c n) =
      C0Seq.pairingL (x + L1Seq.positiveOperator u) a -
        2 * ⟪L1Seq.intervalCoordinateOperator u,
          L1Seq.intervalCoordinateOperator a⟫_ℝ -
        C0Seq.pairingL d u * C0Seq.pairingL d a)
