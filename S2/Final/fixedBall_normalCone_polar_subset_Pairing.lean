/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

/-!
# Coordinate dual-pairing compatibility alias

This module preserves the source-facing `C0Seq.dualPairing` name for the
canonical coordinate dual pairing.
-/

public section

namespace C0Seq

/-- The canonical coordinate dual pairing between real `C0Seq` and real `L1Seq`. -/
noncomputable abbrev dualPairing : DualPairing C0Seq L1Seq :=
  coordinateDualPairing

end C0Seq
