module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LeftDyadicVertex.Asymptotics

public section

open Filter Topology

/- Lemma 6.5b (Left vertices converge to the ghost and satisfy the cone bound) (1):
the negative coordinates of the selected left vertices converge to zero. -/
#check (Lorentz.leftVertex_tendsto_ghost :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)),
    Tendsto
      (fun k ↦ Lorentz.negativeCoordinate d hd
        (Lorentz.leftVertex d hd h_missing z₀ k))
      atTop (𝓝 0))

/- Lemma 6.5b (Left vertices converge to the ghost and satisfy the cone bound) (2):
every selected left vertex satisfies the strict bound from its time to ghost time `1`;
this all-index bound entails the stated eventual future-cone consequence. -/
#check (Lorentz.leftVertex_norm_lt :
  ∀ (d : C0Seq) (hd : d ≠ 0)
    (h_missing : d ∉ Set.range L1Seq.positiveOperator)
    (z₀ : Lorentz.parametrizedSubspace d)
    (_ : ‖Lorentz.negativeCoordinate d hd z₀‖ < (1 / 32 : ℝ)),
    ∀ k, ‖Lorentz.negativeCoordinate d hd
      (Lorentz.leftVertex d hd h_missing z₀ k)‖ <
        1 - Lorentz.leftTime k)
