/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Lipschitz

/-!
# Slope bounds for left vertices

This module exposes the strict subunit slope estimate between adjacent left
dyadic vertices.
-/

public section

namespace Lorentz

/- Lemma 6.5a (Adjacent left-vertex slope estimate): every adjacent pair of
selected left vertices has negative-coordinate displacement strictly smaller
than its dyadic time gap. -/
#check (Lorentz.leftVertex_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : parametrizedSubspace d),
    ‖negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ) → ∀ k : ℕ,
      ‖negativeCoordinate d hd (leftVertex d hd h_missing z₀ (k + 1)) -
          negativeCoordinate d hd (leftVertex d hd h_missing z₀ k)‖ <
        leftTime (k + 1) - leftTime k)

end Lorentz
