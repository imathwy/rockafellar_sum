/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding

/-!
# Lorentz Embedding API

This module records the canonical embedding and image membership criterion.
-/

#check (Lorentz.embedding : ∀ (d : C0Seq), d ≠ 0 →
  Lorentz.parametrizedSubspace d →ₗ[ℝ] ℝ × HilbertProd2 UnitL2)

#check (Lorentz.embedding_apply : ∀ (d : C0Seq) (hd : d ≠ 0)
  (z : Lorentz.parametrizedSubspace d),
  Lorentz.embedding d hd z =
    (Lorentz.positiveCoordinate d hd z, Lorentz.negativeCoordinate d hd z))

#check (Lorentz.embeddingRange : ∀ (d : C0Seq), d ≠ 0 →
  Submodule ℝ (ℝ × HilbertProd2 UnitL2))

#check (Lorentz.mem_embeddingRange : ∀ (d : C0Seq) (hd : d ≠ 0)
  (y : ℝ × HilbertProd2 UnitL2),
  y ∈ Lorentz.embeddingRange d hd ↔
    ∃ z : Lorentz.parametrizedSubspace d, Lorentz.embedding d hd z = y)
