module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorIndex.Pairing
public import S2.GhostCurve.exists_detector_pair_sign

public section

open Topology

/- Along the occurrence subsequence of a favorable detector triple, the signed
detector readings converge to the absolute value of its detector functional. -/
#check (Lorentz.signedDetectorReading_tendsto :
  ∀ (d : C0Seq) (hd : d ≠ 0)
      (h_missing : d ∉ Set.range L1Seq.positiveOperator)
      (w : C0Seq × L1Seq) (_ : w ∉ Lorentz.parametrizedSubspace d)
      (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
      (hN : ∀ p q (h_pq : p < q),
        Filter.Tendsto
          (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
          Filter.atTop (nhds 0))
      (_ : ∀ p q (h_pq : p < q),
        Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
          Filter.atTop (nhds (Lorentz.detectorFunctional d p q w)))
      (t : DetectorTriple)
      (_ : 0 < (t.sign : ℝ) * Lorentz.detectorFunctional d t.p t.q w),
    Filter.Tendsto
      (fun k ↦ (t.sign : ℝ) * C0Seq.symmetricForm w
        (h t.p t.q t.p_lt_q
          (Lorentz.detectorIndex d hd h_missing h hN
            (DetectorTriple.schedule.occurrence t k))))
      Filter.atTop (nhds |Lorentz.detectorFunctional d t.p t.q w|))

/- Lemma 6.13b (Eventually uniform positive detector reading on hit indices):
along the occurrence subsequence of a favorable triple, the signed detector
reading is eventually bounded below by a fixed positive real number. -/
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
        Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
          Filter.atTop (nhds (Lorentz.detectorFunctional d p q w)))
      (t : DetectorTriple)
      (_ : 0 < (t.sign : ℝ) * Lorentz.detectorFunctional d t.p t.q w),
    ∃ η_w : ℝ, 0 < η_w ∧
      ∀ᶠ k in Filter.atTop,
        η_w ≤ (t.sign : ℝ) * C0Seq.symmetricForm w
          (h t.p t.q t.p_lt_q
            (Lorentz.detectorIndex d hd h_missing h hN
              (DetectorTriple.schedule.occurrence t k))))
