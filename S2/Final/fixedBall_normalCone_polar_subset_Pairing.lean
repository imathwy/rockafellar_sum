module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

public section

namespace C0Seq

/-- The canonical coordinate dual pairing between real `C0Seq` and real `L1Seq`. -/
noncomputable abbrev dualPairing : DualPairing C0Seq L1Seq :=
  coordinateDualPairing

end C0Seq
