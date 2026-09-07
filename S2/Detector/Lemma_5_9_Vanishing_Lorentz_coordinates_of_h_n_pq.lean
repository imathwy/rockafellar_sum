/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.RemoteDetectorCoordinates

/-!
# Vanishing Lorentz coordinates

This module records coordinate and energy limits for remote-detector sequences.
-/

public section

open Topology

/- Lemma 5.9 (Vanishing Lorentz coordinates of $h_n^{pq}$) (1): the positive
Lorentz coordinate of every remote detector point vanishes. -/
#check (Lorentz.positiveCoordinate_remoteDetectorPoint :
  ∀ (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    Lorentz.positiveCoordinate d hd (Lorentz.remoteDetectorPoint d p q c n) = 0)

/- Lemma 5.9 (Vanishing Lorentz coordinates of $h_n^{pq}$) (2): the negative
Lorentz coordinate is `(V aₙ, -d(aₙ))` for the remote-copy difference `aₙ`. -/
#check (Lorentz.negativeCoordinate_remoteDetectorPoint :
  ∀ (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    let a := L1Seq.remoteDetectorDifference d p q c n
    Lorentz.negativeCoordinate d hd (Lorentz.remoteDetectorPoint d p q c n) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a) (-C0Seq.pairingL d a))

/- Lemma 5.9 (Vanishing Lorentz coordinates of $h_n^{pq}$) (3): the negative
Lorentz coordinates of an admissible remote-copy sequence tend to zero. -/
#check (Lorentz.negativeCoordinate_remoteDetectorPoint_tendsto_zero :
  ∀ (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (_ : p < q) (c : ℕ → L1Seq),
    (∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) →
    Filter.Tendsto
      (fun n ↦ Lorentz.negativeCoordinate d hd (Lorentz.remoteDetectorPoint d p q c n))
      Filter.atTop (𝓝 0))

/- Lemma 5.9 (Vanishing Lorentz coordinates of $h_n^{pq}$) (4): the quadratic
pairing of a remote detector point is minus the squared negative-coordinate norm. -/
#check (Lorentz.quadraticPairing_remoteDetectorPoint :
  ∀ (d : C0Seq) (hd : d ≠ 0) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ),
    C0Seq.quadraticPairing (Lorentz.remoteDetectorPoint d p q c n) =
      -‖Lorentz.negativeCoordinate d hd (Lorentz.remoteDetectorPoint d p q c n)‖ ^ 2)

/- Lemma 5.9 (Vanishing Lorentz coordinates of $h_n^{pq}$) (5): the quadratic
pairings of an admissible remote detector sequence tend to zero. -/
#check (Lorentz.quadraticPairing_remoteDetectorPoint_tendsto_zero :
  ∀ (d : C0Seq) (_ : d ≠ 0) (p q : ℕ) (_ : p < q) (c : ℕ → L1Seq),
    (∀ n,
      Function.support (fun m ↦ c n m) ⊆ Set.Ioi n ∧
        ‖c n‖ = ‖L1Seq.twoDet d p q‖ ∧
        ‖L1Seq.intervalCoordinateOperator (c n) -
            L1Seq.intervalCoordinateOperator (L1Seq.twoDet d p q)‖ <
          1 / (n + 1 : ℝ)) →
    Filter.Tendsto
      (fun n ↦ C0Seq.quadraticPairing (Lorentz.remoteDetectorPoint d p q c n))
      Filter.atTop (𝓝 0))
