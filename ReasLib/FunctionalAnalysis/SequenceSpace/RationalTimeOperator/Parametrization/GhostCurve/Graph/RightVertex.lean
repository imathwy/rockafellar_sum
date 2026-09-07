module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Graph

public section

namespace Lorentz

/-- Each folded right-hand detector vertex is a point of the ghost graph. -/
theorem rightVertex_mem_ghostGraph
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (i : ℕ) :
    (rightVertex d hd h_missing h h_tendsto i : C0Seq × L1Seq) ∈
      ghostGraph d hd h_missing zLeft z₀ h h_tendsto v := by
  rw [mem_ghostGraph]
  constructor
  · intro heq
    have hrt : (1 : ℝ) < DetectorTriple.rightTime i := by
      rw [DetectorTriple.rightTime_def]
      have hp : 0 < (2 : ℝ) ^ (-(i + 1 : ℝ)) := by positivity
      linarith
    have hp := positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto i
    linarith
  · have hrv := ghostCurveN_rightTime d hd h_missing zLeft z₀ h h_tendsto v i
    have hp := positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto i
    rw [hp]
    exact hrv.symm

/-- The pairing gap against each folded right-hand detector vertex is bounded by
the quadratic pairing of every point in the monotone polar of the ghost graph. -/
theorem rightVertex_gap_le
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (zLeft z₀ : parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (w : C0Seq × L1Seq)
    (hw : w ∈ C0Seq.monotonePolar
      (ghostGraph d hd h_missing zLeft z₀ h h_tendsto v)) (i : ℕ) :
    C0Seq.symmetricForm w (rightVertex d hd h_missing h h_tendsto i) -
        C0Seq.quadraticPairing (rightVertex d hd h_missing h h_tendsto i) ≤
      C0Seq.quadraticPairing w := by
  have hmem := rightVertex_mem_ghostGraph d hd h_missing zLeft z₀ h h_positive h_tendsto v i
  have hpolar := (C0Seq.mem_monotonePolar _ w).1 hw
  have hq := hpolar (rightVertex d hd h_missing h h_tendsto i)
    hmem
  rw [C0Seq.quadraticPairing_sub] at hq
  linarith

end Lorentz
