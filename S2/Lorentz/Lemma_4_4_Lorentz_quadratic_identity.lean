module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEnergy

/- Lemma 4.4 (Lorentz quadratic identity) (1): the quadratic pairing of a
parametrized point is the representative-level operator expression. -/
#check (Lorentz.quadraticPairing_parametrization :
  ∀ (d : C0Seq) (a : L1Seq) (t : ℝ),
    C0Seq.quadraticPairing (Lorentz.parametrization d (a, t)) =
      -(‖L1Seq.intervalCoordinateOperator a‖ ^ 2) + t * C0Seq.pairingL d a)

/- The quadratic pairing on the parametrized subspace is its intrinsic Lorentz
energy. -/
#check (Lorentz.quadraticPairing_eq_energy :
  ∀ (d : C0Seq) (hd : d ≠ 0) (z : Lorentz.parametrizedSubspace d),
    C0Seq.quadraticPairing z =
      Lorentz.energy
        (Lorentz.positiveCoordinate d hd z, Lorentz.negativeCoordinate d hd z))

/- Lemma 4.4 (Lorentz quadratic identity) (2): the intrinsic Lorentz energy is
the square of the positive coordinate minus the squared norm of the negative
coordinate. -/
#check (Lorentz.quadraticIdentity :
  ∀ (d : C0Seq) (hd : d ≠ 0) (z : Lorentz.parametrizedSubspace d),
    C0Seq.quadraticPairing z =
      Lorentz.positiveCoordinate d hd z ^ 2 -
        ‖Lorentz.negativeCoordinate d hd z‖ ^ 2)
