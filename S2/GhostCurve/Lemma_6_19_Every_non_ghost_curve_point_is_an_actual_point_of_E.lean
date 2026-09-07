module

public import ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.GhostCurve.Realization

/- Lemma 6.19 (Every non-ghost curve point is an actual point of $E$): with
`E = Lorentz.embeddingRange d hd` and `f = Lorentz.ghostCurveN ...`, every
`P ≠ 1` gives `(P, f P) ∈ E`. -/
#check Lorentz.ghostCurveN_mem_embeddingRange
