module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Bilinear

public section

open scoped InnerProductSpace

/- Lemma 3.5a (Typed bilinear form associated with A) (1): the continuous bilinear
form obtained by pairing the positive operator with a second `L1Seq` argument. -/
#check (L1Seq.positiveOperatorForm : L1Seq →L[ℝ] L1Seq →L[ℝ] ℝ)

#check (L1Seq.positiveOperatorForm_apply :
  ∀ a b : L1Seq,
    L1Seq.positiveOperatorForm a b =
      C0Seq.pairingL (L1Seq.positiveOperator a) b)

/- Lemma 3.5a (Typed bilinear form associated with A) (2): twice the real Hilbert
inner product after applying the interval-coordinate operator in both arguments. -/
#check (L1Seq.intervalCoordinateForm : L1Seq →L[ℝ] L1Seq →L[ℝ] ℝ)

#check (L1Seq.intervalCoordinateForm_apply :
  ∀ a b : L1Seq,
    L1Seq.intervalCoordinateForm a b =
      2 * ⟪L1Seq.intervalCoordinateOperator a, L1Seq.intervalCoordinateOperator b⟫_ℝ)

#check (L1Seq.flip_intervalCoordinateForm :
  L1Seq.intervalCoordinateForm.flip = L1Seq.intervalCoordinateForm)

#check (L1Seq.intervalCoordinateForm_comm :
  ∀ a b : L1Seq,
    L1Seq.intervalCoordinateForm a b = L1Seq.intervalCoordinateForm b a)
