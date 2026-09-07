/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.JointCoordinateMap.DenseRange

/-!
# Approximation of a prescribed coordinate triple

This module exposes simultaneous approximation of positive, interval, and
pairing coordinates by one `L1Seq` parameter.
-/

public section

/-
Lemma 4.10a (Approximation of the prescribed triple by Θ): one sequence simultaneously
approximates the prescribed positive, interval, and pairing coordinates.
-/
#check (L1Seq.exists_a_approx_target_triple :
  ∀ (d : C0Seq), d ∉ Set.range L1Seq.positiveOperator →
    ∀ (p : ℝ) (x₀ : C0Seq) (v : UnitL2) (r ε : ℝ), 0 < ε →
      ∃ a : L1Seq,
        ‖L1Seq.positiveOperator a - ((p + r) • d - x₀)‖ < ε ∧
        ‖L1Seq.intervalCoordinateOperator a - v‖ < ε ∧
        ‖C0Seq.pairingL d a - (p - r)‖ < ε)
