module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

/- Definition 1.1 (Quadratic pairing, symmetric form, and monotone polar) (1) -/
#check (C0Seq.quadraticPairing_apply :
  (x : C0Seq) → (a : L1Seq) →
    C0Seq.quadraticPairing (x, a) = C0Seq.pairingL x a)

/- Definition 1.1 (Quadratic pairing, symmetric form, and monotone polar) (2) -/
#check (C0Seq.symmetricForm_apply :
  (x y : C0Seq) → (a b : L1Seq) →
    C0Seq.symmetricForm (x, a) (y, b) =
      C0Seq.pairingL x b + C0Seq.pairingL y a)

/- Definition 1.1 (Quadratic pairing, symmetric form, and monotone polar) (3) -/
#check (C0Seq.mem_monotonePolar :
  (S : Set (C0Seq × L1Seq)) → (z : C0Seq × L1Seq) →
    z ∈ C0Seq.monotonePolar S ↔
      ∀ s ∈ S, 0 ≤ C0Seq.quadraticPairing (z - s))
