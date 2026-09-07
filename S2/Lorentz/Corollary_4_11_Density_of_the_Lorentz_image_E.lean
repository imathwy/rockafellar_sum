/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.DenseRange

/-!
# Density of the Lorentz Image

This module exposes density of fixed-coordinate fibers and the full Lorentz image.
-/

public section

namespace Lorentz

/- Corollary 4.11 (Density of the Lorentz image $E$) (1): for every fixed
positive coordinate, the corresponding negative-coordinate fiber is dense. -/
#check (negativeCoordinate_fiber_dense :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (_ : d ∉ Set.range L1Seq.positiveOperator) (p : ℝ),
    Dense (negativeCoordinate d hd ''
      {z : parametrizedSubspace d | positiveCoordinate d hd z = p}))

/- Corollary 4.11 (Density of the Lorentz image $E$) (2): the Lorentz image
`embeddingRange d hd` is dense in `ℝ × HilbertProd2 UnitL2`. -/
#check (embeddingRange_dense :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (_ : d ∉ Set.range L1Seq.positiveOperator),
    Dense (embeddingRange d hd : Set (ℝ × HilbertProd2 UnitL2)))

end Lorentz
