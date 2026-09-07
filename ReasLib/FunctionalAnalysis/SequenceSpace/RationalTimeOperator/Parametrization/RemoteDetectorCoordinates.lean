/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorPoint
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteDetectorDifference

/-!
# Remote-detector coordinates

This module computes Lorentz coordinates and energy limits for remote-detector points.
-/

public section

open Topology

namespace Lorentz

/-- The positive Lorentz coordinate of every remote detector point vanishes. -/
theorem positiveCoordinate_remoteDetectorPoint
    (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    positiveCoordinate d hd (remoteDetectorPoint d p q c n) = 0 := by
  -- Expose the canonical parametrized point and compute its positive coordinate.
  rw [remoteDetectorPoint_apply, positiveCoordinate_apply]
  simp

/-- The negative Lorentz coordinate of a remote detector point consists of the
interval-coordinate image and the negative pairing of its defining difference. -/
theorem negativeCoordinate_remoteDetectorPoint
    (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    let a := L1Seq.remoteDetectorDifference d p q c n
    negativeCoordinate d hd (remoteDetectorPoint d p q c n) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a) (-C0Seq.pairingL d a) := by
  -- Unfold the displayed difference and compute both components of the coordinate.
  dsimp
  rw [remoteDetectorPoint_apply, negativeCoordinate_apply]
  congr 1
  ring

/-- The negative Lorentz coordinates of an admissible remote-detector sequence
tend to zero. -/
theorem negativeCoordinate_remoteDetectorPoint_tendsto_zero
    (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (h_pq : p < q) (c : ℕ → L1Seq)
    (h_copy : ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) :
    Filter.Tendsto
      (fun n ↦ negativeCoordinate d hd (remoteDetectorPoint d p q c n))
      Filter.atTop (𝓝 0) := by
  -- Obtain convergence of the two components from the remote-difference estimates.
  have hI := L1Seq.remoteDetectorDifference_norm_image_tendsto_zero d p q h_pq c h_copy
  have hP := L1Seq.remoteDetectorDifference_pairing_self_tendsto_zero d p q h_pq c h_copy
  have hI' : Filter.Tendsto
      (fun n ↦ L1Seq.intervalCoordinateOperator
        (L1Seq.remoteDetectorDifference d p q c n))
      Filter.atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hI
  -- Combine the component limits in the ordinary product topology.
  have hpair : Filter.Tendsto
      (fun n ↦ (L1Seq.intervalCoordinateOperator
        (L1Seq.remoteDetectorDifference d p q c n),
        -C0Seq.pairingL d (L1Seq.remoteDetectorDifference d p q c n)))
      Filter.atTop (𝓝 (0, 0)) := by
    simpa only [nhds_prod_eq, neg_zero] using hI'.prodMk hP.neg
  -- The canonical map from the product into `HilbertProd2` is continuous.
  have hmk : Continuous (fun z : UnitL2 × ℝ ↦ HilbertProd2.mk z.1 z.2) := by
    change Continuous (WithLp.toLp 2 ∘ fun z : UnitL2 × ℝ ↦ (z.1, z.2))
    exact (WithLp.prod_continuous_toLp 2 UnitL2 ℝ).comp continuous_id
  have hmapped := hmk.continuousAt.tendsto.comp hpair
  -- Rewrite the mapped sequence pointwise as the negative Lorentz coordinate.
  have hpointwise (n : ℕ) :
      negativeCoordinate d hd (remoteDetectorPoint d p q c n) =
        HilbertProd2.mk
          (L1Seq.intervalCoordinateOperator (L1Seq.remoteDetectorDifference d p q c n))
          (-C0Seq.pairingL d (L1Seq.remoteDetectorDifference d p q c n)) := by
    simpa only using negativeCoordinate_remoteDetectorPoint d hd p q c n
  have heq : (fun n ↦ negativeCoordinate d hd (remoteDetectorPoint d p q c n)) =ᶠ[Filter.atTop]
      (fun n ↦ HilbertProd2.mk
        (L1Seq.intervalCoordinateOperator (L1Seq.remoteDetectorDifference d p q c n))
        (-C0Seq.pairingL d (L1Seq.remoteDetectorDifference d p q c n))) :=
    Filter.Eventually.of_forall hpointwise
  have hresult := Filter.Tendsto.congr' heq.symm hmapped
  -- Identify the image of the product zero with zero in `HilbertProd2`.
  have hzero : HilbertProd2.mk (0 : UnitL2) 0 = (0 : HilbertProd2 UnitL2) := by
    apply HilbertProd2.ext
    · rfl
    · rfl
  simpa only [hzero] using hresult

/-- The quadratic pairing of a remote detector point is the negative square of
the norm of its negative Lorentz coordinate. -/
theorem quadraticPairing_remoteDetectorPoint
    (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    C0Seq.quadraticPairing (remoteDetectorPoint d p q c n) =
      -‖negativeCoordinate d hd (remoteDetectorPoint d p q c n)‖ ^ 2 := by
  -- Specialize the Lorentz quadratic identity and eliminate the positive coordinate.
  rw [quadraticIdentity d hd]
  rw [positiveCoordinate_remoteDetectorPoint]
  norm_num

/-- The quadratic pairings of an admissible remote-detector sequence tend to zero. -/
theorem quadraticPairing_remoteDetectorPoint_tendsto_zero
    (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (h_pq : p < q) (c : ℕ → L1Seq)
    (h_copy : ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) :
    Filter.Tendsto
      (fun n ↦ C0Seq.quadraticPairing (remoteDetectorPoint d p q c n))
      Filter.atTop (𝓝 0) := by
  -- Send the negative-coordinate limit successively through norm and squaring.
  have hN := negativeCoordinate_remoteDetectorPoint_tendsto_zero d hd p q h_pq c h_copy
  have hnorm : Filter.Tendsto
      (fun n ↦ ‖negativeCoordinate d hd (remoteDetectorPoint d p q c n)‖)
      Filter.atTop (𝓝 0) := by simpa using hN.norm
  have hsq : Filter.Tendsto
      (fun n ↦ ‖negativeCoordinate d hd (remoteDetectorPoint d p q c n)‖ ^ 2)
      Filter.atTop (𝓝 0) := by
    convert (continuousAt_pow 0 2).tendsto.comp hnorm using 1
    · ext n
      rfl
    · norm_num
  have hneg := hsq.neg
  -- Replace the transformed sequence by the quadratic pairing using the pointwise identity.
  have heq : (fun n ↦ C0Seq.quadraticPairing (remoteDetectorPoint d p q c n)) =ᶠ[Filter.atTop]
      (fun n ↦ -‖negativeCoordinate d hd (remoteDetectorPoint d p q c n)‖ ^ 2) :=
    Filter.Eventually.of_forall (fun n ↦ quadraticPairing_remoteDetectorPoint d hd p q c n)
  simpa only [neg_zero] using hneg.congr' heq.symm

end Lorentz
