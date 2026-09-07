module

public import S2.Basic.Definition_1_1_Quadratic_pairing_symmetric_form_and_monotone_polar

/- Lemma 1.2 (Quadratic difference identity): for all `z w : C0Seq × L1Seq`,
`C0Seq.quadraticPairing (z - w)` is the sum of their quadratic pairings minus
`C0Seq.symmetricForm z w`. -/
#check (C0Seq.quadraticPairing_sub : (z w : C0Seq × L1Seq) →
  C0Seq.quadraticPairing (z - w) = C0Seq.quadraticPairing z + C0Seq.quadraticPairing w -
    C0Seq.symmetricForm z w)
