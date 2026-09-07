/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Asymptotics
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding
public import ReasLib.Analysis.AffineInterpolation
public import ReasLib.Analysis.Normed.LorentzCone

/-!
# Left dyadic Lorentz-cone bounds

This module proves future-cone and nonnegative-energy properties for left
dyadic vertices and their affine edges.
-/

public section

namespace Lorentz

/-- Every selected left dyadic vertex lies in the future Lorentz cone. -/
theorem leftVertex_mem_futureCone (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ) :
    embedding d hd (leftVertex d hd h_missing z₀ k) ∈
      futureCone (HilbertProd2 UnitL2) := by
  rw [embedding_apply, mem_futureCone]
  rw [positiveCoordinate_leftVertex d hd h_missing z₀ k]
  have hnorm := leftVertex_norm_lt d hd h_missing z₀ hN₀ k
  have htime : (1 : ℝ) / 2 ≤ leftTime k := by
    rw [leftTime_def]
    have hi : (0 : ℝ) ≤ k := by positivity
    have hexp : -(k + 1 : ℝ) ≤ (-1 : ℝ) := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hpow' : (2 : ℝ) ^ (-(k + 1 : ℝ)) ≤ (1 : ℝ) / 2 := by
      convert hpow using 1
      ring
    linarith
  exact hnorm.le.trans (by linarith)

/-- The affine edge between consecutive selected left dyadic vertices lies in
the future Lorentz cone. -/
theorem leftVertexEdge_mem_futureCone (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)) (k : ℕ) :
    Set.MapsTo
      (fun P : ℝ ↦
        AffineMap.lineMap
          (embedding d hd (leftVertex d hd h_missing z₀ k))
          (embedding d hd (leftVertex d hd h_missing z₀ (k + 1)))
          ((P - leftTime k) / (leftTime (k + 1) - leftTime k)))
      (Set.Icc (leftTime k) (leftTime (k + 1)))
      (futureCone (HilbertProd2 UnitL2)) := by
  intro P hP
  apply (convex_futureCone (HilbertProd2 UnitL2)).lineMap_mem
    (leftVertex_mem_futureCone d hd h_missing z₀ hN₀ k)
    (leftVertex_mem_futureCone d hd h_missing z₀ hN₀ (k + 1))
  have hgap : 0 < leftTime (k + 1) - leftTime k := by
    rw [leftTime_succ_sub]
    positivity
  constructor
  · exact div_nonneg (sub_nonneg.mpr hP.1) hgap.le
  · apply (div_le_one hgap).2
    linarith [hP.2]

/-- Every point of the affine edge between consecutive selected left dyadic
vertices has nonnegative Lorentz energy. -/
theorem leftVertexEdge_energy_nonneg (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d)
    (hN₀ : ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ))
    (k : ℕ) (P : ℝ) (hP : P ∈ Set.Icc (leftTime k) (leftTime (k + 1))) :
    0 ≤ energy
      (AffineMap.lineMap
        (embedding d hd (leftVertex d hd h_missing z₀ k))
        (embedding d hd (leftVertex d hd h_missing z₀ (k + 1)))
        ((P - leftTime k) / (leftTime (k + 1) - leftTime k))) := by
  apply energy_nonneg_of_mem_futureCone
  exact leftVertexEdge_mem_futureCone d hd h_missing z₀ hN₀ k hP


end Lorentz
