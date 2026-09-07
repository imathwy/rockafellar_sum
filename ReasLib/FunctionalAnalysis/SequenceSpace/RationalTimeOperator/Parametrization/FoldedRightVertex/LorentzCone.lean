/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding
public import ReasLib.Analysis.AffineInterpolation
public import ReasLib.Analysis.Normed.LorentzCone

/-!
# Lorentz-cone bounds for folded vertices

This module places folded right vertices and their affine edges in the future
Lorentz cone.
-/

public section

namespace Lorentz

/-- Every folded right vertex lies in the future Lorentz cone. -/
theorem rightVertex_mem_futureCone (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    embedding d hd (rightVertex d hd h_missing h h_tendsto i) ∈
      futureCone (HilbertProd2 UnitL2) := by
  rw [embedding_apply, mem_futureCone]
  rw [positiveCoordinate_rightVertex d hd h_missing h h_positive h_tendsto i]
  have hnorm := norm_negativeCoordinate_rightVertex_lt d hd h_missing h h_tendsto i
  have hradius : DetectorTriple.rightRadius i ≤ (1 : ℝ) := by
    rw [DetectorTriple.rightRadius_def]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hi : (0 : ℝ) ≤ i := by positivity
    linarith
  have htime : (1 : ℝ) ≤ DetectorTriple.rightTime i := by
    rw [DetectorTriple.rightTime_def]
    have hpow : 0 ≤ (2 : ℝ) ^ (-(i + 1 : ℝ)) := by positivity
    linarith
  exact hnorm.le.trans (hradius.trans htime)

/-- The affine edge between consecutive folded right vertices lies in the
future Lorentz cone. -/
theorem rightVertexEdge_mem_futureCone (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0)) (i : ℕ) :
    Set.MapsTo
      (fun P : ℝ ↦
        AffineMap.lineMap
          (embedding d hd (rightVertex d hd h_missing h h_tendsto (i + 1)))
          (embedding d hd (rightVertex d hd h_missing h h_tendsto i))
          ((P - DetectorTriple.rightTime (i + 1)) /
            (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1))))
      (Set.Icc (DetectorTriple.rightTime (i + 1)) (DetectorTriple.rightTime i))
      (futureCone (HilbertProd2 UnitL2)) := by
  intro P hP
  apply (convex_futureCone (HilbertProd2 UnitL2)).lineMap_mem
    (rightVertex_mem_futureCone d hd h_missing h h_positive h_tendsto (i + 1))
    (rightVertex_mem_futureCone d hd h_missing h h_positive h_tendsto i)
  have hgap : 0 < DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1) := by
    rw [DetectorTriple.rightTime_sub_succ]
    positivity
  constructor
  · exact div_nonneg (sub_nonneg.mpr hP.1) hgap.le
  · apply (div_le_one hgap).2
    linarith [hP.2]

/-- Every point of the affine edge between consecutive folded right vertices
has nonnegative Lorentz energy. -/
theorem rightVertexEdge_energy_nonneg (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (i : ℕ) (P : ℝ)
    (hP : P ∈ Set.Icc (DetectorTriple.rightTime (i + 1))
      (DetectorTriple.rightTime i)) :
    0 ≤ energy
      (AffineMap.lineMap
        (embedding d hd (rightVertex d hd h_missing h h_tendsto (i + 1)))
        (embedding d hd (rightVertex d hd h_missing h h_tendsto i))
        ((P - DetectorTriple.rightTime (i + 1)) /
          (DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1)))) := by
  apply energy_nonneg_of_mem_futureCone
  exact rightVertexEdge_mem_futureCone d hd h_missing h h_positive h_tendsto i hP


/-- The affine edge from the outermost folded right vertex to the future-ray
point `(2 : ℝ) • v` lies in the future Lorentz cone. -/
theorem foldedToFutureEdge_mem_futureCone (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16) :
    Set.MapsTo
      (fun P : ℝ ↦
        AffineMap.lineMap
          (embedding d hd (rightVertex d hd h_missing h h_tendsto 0))
          (embedding d hd ((2 : ℝ) • v))
          ((P - (3 / 2 : ℝ)) / (2 - 3 / 2)))
      (Set.Icc (3 / 2 : ℝ) 2) (futureCone (HilbertProd2 UnitL2)) := by
  intro P hP
  have hleft := rightVertex_mem_futureCone
    d hd h_missing h h_positive h_tendsto 0
  have hright : embedding d hd ((2 : ℝ) • v) ∈
      futureCone (HilbertProd2 UnitL2) := by
    rw [embedding_apply, mem_futureCone, map_smul, map_smul, norm_smul]
    rw [hvP]
    norm_num [Real.norm_eq_abs]
    linarith
  apply (convex_futureCone (HilbertProd2 UnitL2)).lineMap_mem hleft hright
  constructor
  · norm_num
    linarith [hP.1]
  · norm_num
    linarith [hP.2]


/-- Every point of the affine edge from the outermost folded right vertex to
the future-ray point `(2 : ℝ) • v` has nonnegative Lorentz energy. -/
theorem foldedToFutureEdge_energy_nonneg (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
    (h_positive : ∀ p q (h_pq : p < q) n,
      positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
        Filter.atTop (nhds 0))
    (v : parametrizedSubspace d) (hvP : positiveCoordinate d hd v = 1)
    (hvN : ‖negativeCoordinate d hd v‖ < (1 : ℝ) / 16)
    (P : ℝ) (hP : P ∈ Set.Icc (3 / 2 : ℝ) 2) :
    0 ≤ energy
      (AffineMap.lineMap
        (embedding d hd (rightVertex d hd h_missing h h_tendsto 0))
        (embedding d hd ((2 : ℝ) • v))
        ((P - (3 / 2 : ℝ)) / (2 - 3 / 2))) := by
  apply energy_nonneg_of_mem_futureCone
  exact foldedToFutureEdge_mem_futureCone
    d hd h_missing h h_positive h_tendsto v hvP hvN hP


end Lorentz
