/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.DyadicDetectorSchedule
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Coordinates
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Lipschitz
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.FoldedRightVertex.Asymptotics

/-!
# Folded Right-Hand Vertex Geometry

This module exposes coordinate, norm, slope, and asymptotic vertex bounds.
-/

public section

open Filter Topology

/- Lemma 6.12 (Geometry of the folded right-hand vertices) (1): the positive
coordinate of each folded right vertex is its scheduled right time. -/
#check (Lorentz.positiveCoordinate_rightVertex :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (_ : ∀ p q (h_pq : p < q) n,
      Lorentz.positiveCoordinate d hd (h p q h_pq n) = 0)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        atTop (𝓝 0)) (i : ℕ),
    Lorentz.positiveCoordinate d hd
      (Lorentz.rightVertex d hd h_missing h h_tendsto i) =
        DetectorTriple.rightTime i)

/- Lemma 6.12 (Geometry of the folded right-hand vertices) (2): the norm of
the negative coordinate of each folded right vertex is below its scheduled radius. -/
#check (Lorentz.norm_negativeCoordinate_rightVertex_lt :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        atTop (𝓝 0)) (i : ℕ),
    ‖Lorentz.negativeCoordinate d hd
      (Lorentz.rightVertex d hd h_missing h h_tendsto i)‖ <
        DetectorTriple.rightRadius i)

/- Lemma 6.12 (Geometry of the folded right-hand vertices) (3): consecutive
scheduled right times have the explicit zero-based dyadic gap. -/
#check (DetectorTriple.rightTime_sub_succ :
  ∀ i : ℕ, DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1) =
    (2 : ℝ) ^ (-(i + 2 : ℝ)))

/- Lemma 6.12 (Geometry of the folded right-hand vertices) (4): consecutive
scheduled radii sum to `3 / 32` times the explicit zero-based dyadic gap. -/
#check (DetectorTriple.rightRadius_add_succ_rpow :
  ∀ i : ℕ, DetectorTriple.rightRadius i + DetectorTriple.rightRadius (i + 1) =
    (3 / 32 : ℝ) * (2 : ℝ) ^ (-(i + 2 : ℝ)))

/- Lemma 6.12 (Geometry of the folded right-hand vertices) (5): consecutive
folded right vertices have negative-coordinate displacement below their time gap. -/
#check (Lorentz.rightVertex_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        atTop (𝓝 0)) (i : ℕ),
    ‖Lorentz.negativeCoordinate d hd
        (Lorentz.rightVertex d hd h_missing h h_tendsto i) -
      Lorentz.negativeCoordinate d hd
        (Lorentz.rightVertex d hd h_missing h h_tendsto (i + 1))‖ <
      DetectorTriple.rightTime i - DetectorTriple.rightTime (i + 1))

/- Lemma 6.12 (Geometry of the folded right-hand vertices) (6): the negative
coordinates of the folded right vertices converge to the ghost coordinate `0`. -/
#check (Lorentz.rightVertex_tendsto_ghost :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (h : ∀ p q : ℕ, p < q → ℕ → Lorentz.parametrizedSubspace d)
    (h_tendsto : ∀ p q (h_pq : p < q),
      Tendsto (fun n ↦ Lorentz.negativeCoordinate d hd (h p q h_pq n))
        atTop (𝓝 0)),
    Tendsto (fun i ↦ Lorentz.negativeCoordinate d hd
      (Lorentz.rightVertex d hd h_missing h h_tendsto i)) atTop (𝓝 0))
