/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Pairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPoint.Pairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteDetectorDifference

/-!
# Remote-detector pairing limits

This module records the asymptotic pairing limit for admissible remote-copy
families.
-/

public section

open Topology
open scoped InnerProductSpace

namespace Lorentz

/-- Pairing a fixed point with the remote detector points of an admissible
remote-copy family tends to its two-coordinate detector-functional reading. -/
theorem remoteDetectorPoint_pairing_tendsto
    (d : C0Seq) (w : C0Seq × L1Seq) (p q : ℕ) (h_pq : p < q) (c : ℕ → L1Seq)
    (h_copy : ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) :
    Filter.Tendsto
      (fun n ↦ C0Seq.symmetricForm w (remoteDetectorPoint d p q c n))
      Filter.atTop (𝓝 (detectorFunctional d p q w)) := by
  rcases w with ⟨x, u⟩
  let a : ℕ → L1Seq := fun n ↦ L1Seq.remoteDetectorDifference d p q c n
  have hpair :
      Filter.Tendsto (fun n ↦ C0Seq.pairingL (x + L1Seq.positiveOperator u) (a n))
        Filter.atTop
        (𝓝 (C0Seq.pairingL (x + L1Seq.positiveOperator u) (L1Seq.twoDet d p q))) := by
    simpa [a] using
      (L1Seq.remoteDetectorDifference_pairing_tendsto d p q h_pq c h_copy
        (x + L1Seq.positiveOperator u))
  -- Convert the quantitative norm convergence into convergence of the
  -- interval-coordinate vectors themselves.
  have hnorm :
      Filter.Tendsto (fun n ↦ ‖L1Seq.intervalCoordinateOperator (a n)‖)
        Filter.atTop (𝓝 0) := by
    simpa [a] using
      (L1Seq.remoteDetectorDifference_norm_image_tendsto_zero d p q h_pq c h_copy)
  have himage :
      Filter.Tendsto (fun n ↦ L1Seq.intervalCoordinateOperator (a n))
        Filter.atTop (𝓝 (0 : UnitL2)) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  -- Continuity of the inner product sends the vanishing vector term to zero.
  have hinner :
      Filter.Tendsto
        (fun n ↦ ⟪L1Seq.intervalCoordinateOperator u,
          L1Seq.intervalCoordinateOperator (a n)⟫_ℝ)
        Filter.atTop
        (𝓝 ⟪L1Seq.intervalCoordinateOperator u, (0 : UnitL2)⟫_ℝ) := by
    exact tendsto_const_nhds.inner himage
  have hself :
      Filter.Tendsto (fun n ↦ C0Seq.pairingL d (a n)) Filter.atTop (𝓝 0) := by
    simpa [a] using
      (L1Seq.remoteDetectorDifference_pairing_self_tendsto_zero d p q h_pq c h_copy)
  -- Combine the three scalar limits in the expanded symmetric pairing.
  have htotal := (hpair.sub (hinner.const_mul 2)).sub
    (hself.const_mul (C0Seq.pairingL d u))
  have htotal' :
      Filter.Tendsto
        (fun n ↦ C0Seq.pairingL (x + L1Seq.positiveOperator u) (a n) -
          2 * ⟪L1Seq.intervalCoordinateOperator u,
            L1Seq.intervalCoordinateOperator (a n)⟫_ℝ -
          C0Seq.pairingL d u * C0Seq.pairingL d (a n))
        Filter.atTop
        (𝓝 (C0Seq.pairingL (x + L1Seq.positiveOperator u) (L1Seq.twoDet d p q) -
          2 * ⟪L1Seq.intervalCoordinateOperator u, (0 : UnitL2)⟫_ℝ -
          C0Seq.pairingL d u * 0)) := by
    simpa only [Function.comp_apply, mul_zero, sub_zero] using htotal
  -- Rewrite both endpoints through the public pairing and detector interfaces.
  simpa only [a, symmetricForm_remoteDetectorPoint, detectorFunctional_apply,
    inner_zero_right, mul_zero, sub_zero] using htotal'

end Lorentz
