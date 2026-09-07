/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive
public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding

/-!
# Dense Lorentz fibers

This module proves density of the negative-coordinate image at a fixed positive
coordinate.
-/

public section

namespace Lorentz

/-- For every fixed positive coordinate, the image of the corresponding fiber
under the negative Lorentz coordinate is dense. -/
theorem negativeCoordinate_fiber_dense
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) (p : ℝ) :
    Dense (negativeCoordinate d hd ''
      {z : parametrizedSubspace d | positiveCoordinate d hd z = p}) := by
  -- It suffices to put a point of the fixed-coordinate image in every metric ball.
  rw [Metric.dense_iff]
  intro y ε hε
  -- Joint approximation fixes the positive coordinate and approximates both axes of `y`.
  obtain ⟨z, hzP, _, hzN⟩ :=
    exists_approx_fixedPositiveCoordinate d hd h_missing p 0
      (HilbertProd2.fst y) (HilbertProd2.snd y) ε hε
  refine ⟨negativeCoordinate d hd z, ?_, ?_⟩
  · -- Reconstructing `y` from its coordinates turns the norm estimate into ball membership.
    simpa only [Metric.mem_ball, dist_eq_norm, HilbertProd2.mk_fst_snd] using hzN
  · -- The exact positive-coordinate equation places `z` in the required fiber.
    exact ⟨z, hzP, rfl⟩

/-- The range of the Lorentz embedding is dense in the product of its positive
and negative coordinate spaces. -/
theorem embeddingRange_dense
    (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator) :
    Dense (embeddingRange d hd : Set (ℝ × HilbertProd2 UnitL2)) := by
  -- Work fiberwise over the first coordinate of an arbitrary target product point.
  rw [Metric.dense_iff]
  rintro ⟨p, y⟩ ε hε
  obtain ⟨y', hy'fiber, hy'dist⟩ :=
    (negativeCoordinate_fiber_dense d hd h_missing p).exists_dist_lt y hε
  rcases hy'fiber with ⟨z, hzP, rfl⟩
  refine ⟨(p, negativeCoordinate d hd z), ?_, ?_⟩
  · -- Equal first coordinates reduce the product distance to the fiber estimate.
    simpa only [Metric.mem_ball, dist_prod_same_left, dist_comm] using hy'dist
  · -- The same source point witnesses membership in the embedding range.
    refine (mem_embeddingRange d hd _).2 ?_
    refine ⟨z, ?_⟩
    rw [embedding_apply, hzP]

end Lorentz
