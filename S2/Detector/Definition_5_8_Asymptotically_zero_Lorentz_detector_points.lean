/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPoint

/-!
# Asymptotically Zero Lorentz Detector Points

This module records the parametrized form of remote detector points.
-/

public section

/- Definition 5.8 (Asymptotically zero-Lorentz detector points): for fixed ordered
coordinates and a chosen remote-copy sequence, `hₙ = Ψ(aₙ, -C0Seq.pairingL d aₙ)`
is an element of `Lorentz.parametrizedSubspace d`. -/
#check (Lorentz.remoteDetectorPoint_apply :
  ∀ (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    let a := L1Seq.remoteDetectorDifference d p q c n
    Lorentz.remoteDetectorPoint d p q c n =
      Lorentz.parametrizedPoint d a (-C0Seq.pairingL d a))
