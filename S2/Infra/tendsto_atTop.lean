module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0

public section

open Topology

/- Infrastructure A.2 (c₀ membership as coordinate convergence) (1): every real
zero-at-infinity sequence converges coordinatewise to zero along `Filter.atTop`. -/
#check (C0Seq.tendsto_zero :
  ∀ x : C0Seq, Filter.Tendsto x Filter.atTop (𝓝 0))

/- Infrastructure A.2 (c₀ membership as coordinate convergence) (2): a real sequence
tending to zero along `Filter.atTop` defines an element of `C0Seq`. -/
#check (C0Seq.ofTendsto :
  (x : ℕ → ℝ) → Filter.Tendsto x Filter.atTop (𝓝 0) → C0Seq)

/- The constructed element of `C0Seq` has the original coordinates. -/
#check (C0Seq.ofTendsto_apply :
  ∀ (x : ℕ → ℝ) (hx : Filter.Tendsto x Filter.atTop (𝓝 0)) (n : ℕ),
    C0Seq.ofTendsto x hx n = x n)
