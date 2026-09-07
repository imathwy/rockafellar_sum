module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

public section

namespace Lorentz

/-- The symmetric pairing minus the quadratic pairing at a folded right vertex
separates into its signed detector, base, cross, and perturbation terms. -/
theorem symmetricForm_rightVertex_sub_quadraticPairing
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (w : C0Seq × L1Seq) (i : ℕ) :
    let ξ := nearGhostBase d hd h_missing i
    let δ := detectorPerturbation d hd h_missing h h_tendsto i
    let m := rightVertex d hd h_missing h h_tendsto i
    let hᵢ := scheduledDetectorPoint h i
      (detectorIndex d hd h_missing h h_tendsto i)
    C0Seq.symmetricForm w m - C0Seq.quadraticPairing m =
      (((DetectorTriple.schedule.toFun i).sign : ℝ) *
          detectorScale d hd h_missing i) * C0Seq.symmetricForm w hᵢ +
          C0Seq.symmetricForm w ξ - C0Seq.quadraticPairing ξ -
          C0Seq.symmetricForm ξ δ - C0Seq.quadraticPairing δ := by
  -- Expose the four named terms, then replace the vertex by its base-plus-perturbation form.
  dsimp
  rw [rightVertex_apply, Submodule.coe_add]
  -- Linearity separates the symmetric pairing into its base and perturbation terms.
  rw [map_add]
  -- Convert the available quadratic subtraction identity into the required addition formula.
  have hqadd : C0Seq.quadraticPairing
      ((nearGhostBase d hd h_missing i : C0Seq × L1Seq) +
        (detectorPerturbation d hd h_missing h h_tendsto i : C0Seq × L1Seq)) =
      C0Seq.quadraticPairing (nearGhostBase d hd h_missing i) +
        C0Seq.quadraticPairing (detectorPerturbation d hd h_missing h h_tendsto i) +
        C0Seq.symmetricForm (nearGhostBase d hd h_missing i)
          (detectorPerturbation d hd h_missing h h_tendsto i) := by
    have hsub := C0Seq.quadraticPairing_sub
      (nearGhostBase d hd h_missing i : C0Seq × L1Seq)
      (-(detectorPerturbation d hd h_missing h h_tendsto i : C0Seq × L1Seq))
    simpa only [sub_neg_eq_add, QuadraticMap.map_neg, map_neg, neg_neg] using hsub
  rw [hqadd]
  -- Rewrite the perturbation as the signed scaled detector and move the scalar through the form.
  rw [detectorPerturbation_apply, Submodule.coe_smul]
  rw [map_smul]
  -- The remaining equality is the scalar rearrangement of the expanded terms.
  ring

end Lorentz
