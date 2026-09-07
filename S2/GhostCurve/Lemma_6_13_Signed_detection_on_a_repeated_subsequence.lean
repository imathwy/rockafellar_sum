module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector.FavorableSign
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorIndex.Pairing

open Topology

#check (Lorentz.exists_detectorTriple_pos :
  ∀ (d : C0Seq) (w : C0Seq × L1Seq),
    d ≠ 0 → w ∉ Lorentz.parametrizedSubspace d →
      ∃ t : DetectorTriple,
        0 < (t.sign : ℝ) * Lorentz.detectorFunctional d t.p t.q w)

/- Lemma 6.13 (Signed detection on a repeated subsequence)

For an exterior point `w`, choose a favorable detector triple. Along the
repeated occurrence subsequence for that triple, the selected signed detector
readings are eventually bounded below by a fixed positive real number. -/
#check (Lorentz.eventually_pos_signedDetectorReading :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (w : C0Seq × L1Seq) (_ : w ∉ Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (hN : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (_ : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
          Filter.atTop (nhds (Lorentz.detectorFunctional d p q w)))
      (t : DetectorTriple)
      (_ : 0 < (t.sign : ℝ) * Lorentz.detectorFunctional d t.p t.q w),
    ∃ η_w : ℝ, 0 < η_w ∧
      ∀ᶠ k in Filter.atTop,
        η_w ≤ (t.sign : ℝ) * C0Seq.symmetricForm w
          (h t.p t.q t.p_lt_q
            (Lorentz.detectorIndex d hd h_missing h hN
              (DetectorTriple.schedule.occurrence t k))))
