/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzEmbedding.FutureRay

/-!
# Geometry of the future ray

This module records embedding, cone, slope, and energy bounds on the future ray.
-/

/- Lemma 6.17b (Future ray lies in the Lorentz future cone) (1) -/
#check (Lorentz.futureRay_mem_embeddingRange :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d)
    (_ : Lorentz.positiveCoordinate d hd v = 1) (P : ℝ) (_ : 2 ≤ P),
    (P, Lorentz.negativeCoordinate d hd (P • v)) ∈ Lorentz.embeddingRange d hd)

/- Lemma 6.17b (Future ray lies in the Lorentz future cone) (2) -/
#check (Lorentz.futureRay_slope_lt_one :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 →
      ‖Lorentz.negativeCoordinate d hd v‖ < 1)

/- Lemma 6.17b (Future ray lies in the Lorentz future cone) (3) -/
#check (Lorentz.futureRay_negativeCoordinate_bounds :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d),
    ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 →
      ∀ (P : ℝ), 2 ≤ P →
        ‖Lorentz.negativeCoordinate d hd (P • v)‖ < P / 16 ∧ P / 16 ≤ P - 1)

/- Lemma 6.17b (Future ray lies in the Lorentz future cone) (4) -/
#check (Lorentz.futureRay_mem_futureCone :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd v = 1 →
      ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 →
        ∀ (P : ℝ), 2 ≤ P →
          Lorentz.embedding d hd (P • v) ∈
            Lorentz.futureCone (HilbertProd2 UnitL2))

/- Lemma 6.17b (Future ray lies in the Lorentz future cone) (5) -/
#check (Lorentz.futureRay_energy_nonneg :
  ∀ (d : C0Seq) (hd : d ≠ 0) (v : Lorentz.parametrizedSubspace d),
    Lorentz.positiveCoordinate d hd v = 1 →
      ‖Lorentz.negativeCoordinate d hd v‖ < (1 : ℝ) / 16 →
        ∀ (P : ℝ), 2 ≤ P →
          0 ≤ Lorentz.energy (Lorentz.embedding d hd (P • v)))
