module

public import ReasLib.Analysis.LeftDyadicTemplate
public import S2.GhostCurve.Lemma_6_2_A_negative_energy_time_zero_point_away_from_U

public section

open Filter Topology

/- Definition 6.4a (Left dyadic times and strict template) (1): the zero-based
left dyadic times have the formula `1 - 2 ^ (-(k + 1 : ℝ))`. -/
#check (Lorentz.leftTime_def :
  ∀ k : ℕ, Lorentz.leftTime k = 1 - (2 : ℝ) ^ (-(k + 1 : ℝ)))

/- Definition 6.4a (Left dyadic times and strict template) (2): at
`HilbertProd2 UnitL2`, the affine template is `P ↦ (1 - P) • N₀`. -/
#check (Lorentz.leftTemplate_apply :
  ∀ (N₀ : HilbertProd2 UnitL2) (P : ℝ),
    Lorentz.leftTemplate N₀ P = (1 - P) • N₀)

/- Definition 6.4a (Left dyadic times and strict template) (3): successive
left dyadic times differ by `2 ^ (-(k + 2 : ℝ))`. -/
#check (Lorentz.leftTime_succ_sub :
  ∀ k : ℕ,
    Lorentz.leftTime (k + 1) - Lorentz.leftTime k = (2 : ℝ) ^ (-(k + 2 : ℝ)))

/- Definition 6.4a (Left dyadic times and strict template) (4): the left
dyadic times converge to `1`. -/
#check (Lorentz.tendsto_leftTime :
  Tendsto Lorentz.leftTime atTop (𝓝 1))

/- Definition 6.4a (Left dyadic times and strict template) (5): if
`‖N₀‖ < 1 / 32`, the template is `1 / 32`-Lipschitz. -/
#check (Lorentz.lipschitzWith_leftTemplate_one_div_32 :
  ∀ N₀ : HilbertProd2 UnitL2, ‖N₀‖ < (1 / 32 : ℝ) →
    LipschitzWith (1 / 32 : NNReal) (Lorentz.leftTemplate N₀))

/- The exact Lipschitz constant for the affine template is `‖N₀‖₊`. -/
#check (Lorentz.lipschitzWith_leftTemplate :
  ∀ N₀ : HilbertProd2 UnitL2,
    LipschitzWith ‖N₀‖₊ (Lorentz.leftTemplate N₀))
