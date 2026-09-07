module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.Point
public import ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.RemoteCopySequence

public section

noncomputable section

namespace Lorentz

/-- The point obtained by applying the parametrization to a remote-detector difference,
with scalar parameter equal to the negative of its pairing with `d`. -/
def remoteDetectorPoint (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) :
    ℕ → parametrizedSubspace d :=
  fun n ↦
    let a := L1Seq.remoteDetectorDifference d p q c n
    parametrizedPoint d a (-C0Seq.pairingL d a)

/-- Evaluation of a remote detector point at a sequence index. -/
theorem remoteDetectorPoint_apply (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    remoteDetectorPoint d p q c n =
      parametrizedPoint d (L1Seq.remoteDetectorDifference d p q c n)
        (-C0Seq.pairingL d (L1Seq.remoteDetectorDifference d p q c n)) := by
  rfl

/-- The ambient value of a remote detector point is its parametrized pair. -/
theorem coe_remoteDetectorPoint (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    (remoteDetectorPoint d p q c n : C0Seq × L1Seq) =
      parametrization d
        (L1Seq.remoteDetectorDifference d p q c n,
          -C0Seq.pairingL d (L1Seq.remoteDetectorDifference d p q c n)) := by
  rw [remoteDetectorPoint_apply, parametrizedPoint_apply]

/-- The ambient remote detector point belongs to the parametrized subspace. -/
theorem remoteDetectorPoint_mem (d : C0Seq) (p q : ℕ) (c : ℕ → L1Seq) (n : ℕ) :
    (remoteDetectorPoint d p q c n : C0Seq × L1Seq) ∈ parametrizedSubspace d := by
  rw [remoteDetectorPoint_apply, parametrizedPoint_apply]
  exact (mem_parametrizedSubspace d _).mpr
    ⟨L1Seq.remoteDetectorDifference d p q c n,
      -C0Seq.pairingL d (L1Seq.remoteDetectorDifference d p q c n),
      parametrization_apply d _ _⟩

end Lorentz
