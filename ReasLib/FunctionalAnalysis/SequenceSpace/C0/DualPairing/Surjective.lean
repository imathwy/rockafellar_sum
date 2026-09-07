module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

public section

namespace C0Seq

/-- The strong-dual map of the coordinate pairing between real `C0Seq` and real
`L1Seq` is surjective. -/
theorem coordinateDualPairing_surjective :
    Function.Surjective coordinateDualPairing.toDual := by
  intro φ
  refine ⟨dualCoefficients φ, ?_⟩
  rw [coordinateDualPairing_toDual]
  exact l1ToDual_dualCoefficients φ

end C0Seq
