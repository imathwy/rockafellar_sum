module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing.RemoteSupport
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteCopySequence

public section

open Topology

namespace L1Seq

/-- The interval-coordinate image of a remote-detector difference tends to zero
when the supplied remote copies have matching norm and vanishing image error. -/
theorem remoteDetectorDifference_norm_image_tendsto_zero
    (d : C0Seq) (p q : ℕ) (_ : p < q) (c : ℕ → L1Seq)
    (h_copy : ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖twoDet d p q‖ ∧
        ‖intervalCoordinateOperator (c n) - intervalCoordinateOperator (twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) :
    Filter.Tendsto
      (fun n ↦ ‖intervalCoordinateOperator (remoteDetectorDifference d p q c n)‖)
      Filter.atTop (𝓝 0) := by
  -- Linearity identifies the image with the reverse of the controlled error,
  -- so the reciprocal estimate squeezes its norm to zero.
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [remoteDetectorDifference_apply, map_sub, norm_sub_rev]
  exact (h_copy n).2.2.le

/-- Pairing a remote-detector difference with its defining sequence is the
negative pairing with the corresponding remote copy. -/
theorem remoteDetectorDifference_pairing_self
    (d : C0Seq) (p q : ℕ) (h_pq : p < q) (c : ℕ → L1Seq) (n : ℕ) :
    C0Seq.pairingL d (remoteDetectorDifference d p q c n) =
      -C0Seq.pairingL d (c n) := by
  -- Expand the difference, use linearity, and cancel the determinant's
  -- self-pairing.
  rw [remoteDetectorDifference_apply, map_sub,
    C0Seq.pairingL_twoDet_self d p q h_pq, zero_sub]

/-- Pairing a remote-detector difference with any sequence in `C0Seq` tends to
the pairing with its defining two-coordinate determinant vector. -/
theorem remoteDetectorDifference_pairing_tendsto
    (d : C0Seq) (p q : ℕ) (_ : p < q) (c : ℕ → L1Seq)
    (h_copy : ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖twoDet d p q‖ ∧
        ‖intervalCoordinateOperator (c n) - intervalCoordinateOperator (twoDet d p q)‖ <
          1 / (n + 1 : ℝ))
    (x : C0Seq) :
    Filter.Tendsto (fun n ↦ C0Seq.pairingL x (remoteDetectorDifference d p q c n))
      Filter.atTop (𝓝 (C0Seq.pairingL x (twoDet d p q))) := by
  -- The supports escape to infinity while the exact norm identity supplies a
  -- uniform bound, hence the remote-copy pairing vanishes.
  have remotePairingTendsToZero :
      Filter.Tendsto (fun n ↦ C0Seq.pairingL x (c n)) Filter.atTop (𝓝 0) :=
    C0Seq.pairingL_tendsto_zero_of_support_Ioi c ‖twoDet d p q‖
      (fun n ↦ (h_copy n).1) (fun n ↦ (h_copy n).2.1.le) x
  -- Subtract that vanishing pairing from the constant determinant pairing and
  -- normalize the result back to the remote-detector difference.
  simpa only [remoteDetectorDifference_apply, map_sub, sub_zero] using
    tendsto_const_nhds.sub remotePairingTendsToZero

/-- Pairing a remote-detector difference with its defining sequence tends to
zero when the supplied remote copies move their uniformly bounded mass outward. -/
theorem remoteDetectorDifference_pairing_self_tendsto_zero
    (d : C0Seq) (p q : ℕ) (h_pq : p < q) (c : ℕ → L1Seq)
    (h_copy : ∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖twoDet d p q‖ ∧
        ‖intervalCoordinateOperator (c n) - intervalCoordinateOperator (twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) :
    Filter.Tendsto (fun n ↦ C0Seq.pairingL d (remoteDetectorDifference d p q c n))
      Filter.atTop (𝓝 0) := by
  -- Remote support and the common norm make the copy pairings with `d` tend
  -- to zero.
  have remotePairingTendsToZero :
      Filter.Tendsto (fun n ↦ C0Seq.pairingL d (c n)) Filter.atTop (𝓝 0) :=
    C0Seq.pairingL_tendsto_zero_of_support_Ioi c ‖twoDet d p q‖
      (fun n ↦ (h_copy n).1) (fun n ↦ (h_copy n).2.1.le) d
  -- Negation preserves the zero limit, and the pointwise self-pairing identity
  -- identifies the negated sequence with the target.
  simpa only [remoteDetectorDifference_pairing_self d p q h_pq c, neg_zero] using
    remotePairingTendsToZero.neg

end L1Seq
