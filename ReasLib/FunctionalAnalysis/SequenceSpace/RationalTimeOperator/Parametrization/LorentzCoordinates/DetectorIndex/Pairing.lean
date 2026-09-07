module

public import Mathlib.Topology.Order.OrderClosed
public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Detector
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.DetectorIndex

public section

open Topology

namespace Lorentz

/-- Along the occurrence subsequence of a favorable detector triple, the signed
detector readings converge to the absolute value of its detector functional. -/
theorem signedDetectorReading_tendsto
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (w : C0Seq × L1Seq) (_ : w ∉ parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (hN : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (hB : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w)))
    (t : DetectorTriple)
    (ht : 0 < (t.sign : ℝ) * detectorFunctional d t.p t.q w) :
    Filter.Tendsto
      (fun k ↦ (t.sign : ℝ) * C0Seq.symmetricForm w
        (h t.p t.q t.p_lt_q
          (detectorIndex d hd h_missing h hN
            (DetectorTriple.schedule.occurrence t k))))
      Filter.atTop (nhds |detectorFunctional d t.p t.q w|) := by
  -- Infinite repetition makes the occurrence map cofinal in the schedule.
  have hocc : Filter.Tendsto (DetectorTriple.schedule.occurrence t)
      Filter.atTop Filter.atTop :=
    (DetectorTriple.schedule.strictMono_occurrence t).tendsto_atTop
  -- Each chosen detector index dominates its schedule index, so the selected
  -- indices along this occurrence subsequence are cofinal as well.
  have hidx : Filter.Tendsto
      (fun k ↦ detectorIndex d hd h_missing h hN
        (DetectorTriple.schedule.occurrence t k))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro N
    have hocc_event := hocc.eventually (Filter.eventually_ge_atTop N)
    filter_upwards [hocc_event] with k hk
    exact le_trans hk
      (le_detectorIndex d hd h_missing h hN (DetectorTriple.schedule.occurrence t k))
  -- Restrict the detector limit to the cofinal selected indices and multiply
  -- the resulting limit by the fixed favorable sign.
  have hbase := hB t.p t.q t.p_lt_q
  have hread := hbase.comp hidx
  have hsigned := hread.const_mul (t.sign : ℝ)
  -- The favorable sign identifies the signed functional value with its
  -- absolute value in either of the two possible sign cases.
  have hlimit : (t.sign : ℝ) * detectorFunctional d t.p t.q w =
      |detectorFunctional d t.p t.q w| := by
    rcases DetectorTriple.sign_eq_one_or_neg_one t with hsign | hsign
    · have hsignR : (t.sign : ℝ) = 1 := by exact_mod_cast hsign
      rw [hsignR] at ht ⊢
      simpa only [one_mul] using (abs_of_pos ht).symm
    · have hsignR : (t.sign : ℝ) = -1 := by exact_mod_cast hsign
      have hDneg : detectorFunctional d t.p t.q w < 0 := by
        nlinarith [ht]
      rw [hsignR] at ht ⊢
      simpa only [neg_one_mul] using (abs_of_neg hDneg).symm
  -- Rewrite the signed limit into the required absolute-value normal form.
  simpa only [Function.comp_apply, hlimit] using hsigned

/-- Along the occurrence subsequence of a favorable detector triple, the signed
detector reading is eventually bounded below by a fixed positive real number. -/
theorem eventually_pos_signedDetectorReading
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (w : C0Seq × L1Seq) (hw : w ∉ parametrizedSubspace d)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (hN : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (hB : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ C0Seq.symmetricForm w (h p q h_pq n))
        Filter.atTop (nhds (detectorFunctional d p q w)))
    (t : DetectorTriple)
    (ht : 0 < (t.sign : ℝ) * detectorFunctional d t.p t.q w) :
    ∃ η_w : ℝ, 0 < η_w ∧
      ∀ᶠ k in Filter.atTop,
        η_w ≤ (t.sign : ℝ) * C0Seq.symmetricForm w
          (h t.p t.q t.p_lt_q
            (detectorIndex d hd h_missing h hN
              (DetectorTriple.schedule.occurrence t k))) := by
  -- Reuse the established convergence of the signed detector readings.
  have hread := signedDetectorReading_tendsto d hd h_missing w hw h hN hB t ht
  -- Favorability rules out a zero detector functional, hence its absolute
  -- value is strictly positive.
  have hDne : detectorFunctional d t.p t.q w ≠ 0 := by
    intro hD
    simp [hD] at ht
  have habs_pos : 0 < |detectorFunctional d t.p t.q w| := abs_pos.mpr hDne
  -- Half the positive limit is a fixed positive lower bound eventually.
  refine ⟨|detectorFunctional d t.p t.q w| / 2, half_pos habs_pos, ?_⟩
  exact hread.eventually_const_le (half_lt_self habs_pos)

end Lorentz
