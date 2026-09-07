module

public import S2.GhostCurve.foldedDetector_expansion
public import S2.GhostCurve.foldedDetector_remainder_bounds

public section

namespace Lorentz

/- Lemma 6.14 (Exact folded-detector expansion and lower-order bounds) (1):
the exact folded-detector expansion of `B(w, mᵢ) - c(mᵢ)`. -/
#check Lorentz.symmetricForm_rightVertex_sub_quadraticPairing

/- Lemma 6.14 (Exact folded-detector expansion and lower-order bounds) (2):
the detector perturbation `δᵢ` has positive Lorentz coordinate zero. -/
#check Lorentz.positiveCoordinate_detectorPerturbation

/- Lemma 6.14 (Exact folded-detector expansion and lower-order bounds) (3):
the quadratic pairing of `δᵢ` is the negative square of the norm of its
negative Lorentz coordinate. -/
#check Lorentz.quadraticPairing_detectorPerturbation_eq_neg_sq

/- Lemma 6.14 (Exact folded-detector expansion and lower-order bounds) (4):
the quadratic pairing of `δᵢ` is nonpositive. -/
#check Lorentz.quadraticPairing_detectorPerturbation_nonpos

/- Lemma 6.14 (Exact folded-detector expansion and lower-order bounds) (5):
the cross term `|B(ξᵢ, δᵢ)|` is strictly below `ρᵢ ^ 2 / 2`. -/
#check Lorentz.abs_symmetricForm_nearGhostBase_detectorPerturbation_lt

/- Lemma 6.14 (Exact folded-detector expansion and lower-order bounds) (6):
the base energy satisfies `|c(ξᵢ)| ≤ 9 / 4`. -/
#check Lorentz.abs_quadraticPairing_nearGhostBase_le

/- Lemma 6.14 (Exact folded-detector expansion and lower-order bounds) (7):
the ambient pairing satisfies `|B(w, ξᵢ)| ≤ ‖w‖_Z * ‖ξᵢ‖_Z`. -/
#check Lorentz.abs_symmetricForm_nearGhostBase_le_zSize

end Lorentz
