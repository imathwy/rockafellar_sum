/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.ChainInterpolation

/-!
# Lipschitz chain interpolation

This module exposes Lipschitz gluing for increasing and decreasing ordered chains.
-/

public section

open Filter Topology

universe u

/- Infrastructure E.4 (Lipschitz gluing along an ordered chain) (1).
Adjacent affine interpolants along an increasing chain converging to `a` glue to a
`K`-Lipschitz map on `Set.Icc (t 0) a`. -/
#check (AffineMap.lipschitzOnWith_chainInterpolation_of_strictMono :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : NNReal) (a : ℝ) (t : ℕ → ℝ) (x : ℕ → E) (x0 : E) (f : ℝ → E)
    (_ : StrictMono t) (_ : ∀ n, t n < a)
    (_ : Tendsto t atTop (𝓝 a)) (_ : Tendsto x atTop (𝓝 x0))
    (_ : ∀ n, ‖x (n + 1) - x n‖ ≤ (K : ℝ) * |t (n + 1) - t n|)
    (_ : f a = x0)
    (_ : ∀ n, Set.EqOn f
      (fun s ↦ AffineMap.lineMap (x n) (x (n + 1))
        ((s - t n) / (t (n + 1) - t n)))
      (Set.Icc (t n) (t (n + 1)))),
    LipschitzOnWith K f (Set.Icc (t 0) a))

/- Infrastructure E.4 (Lipschitz gluing along an ordered chain) (2).
Adjacent affine interpolants along a decreasing chain converging to `a` glue to a
`K`-Lipschitz map on `Set.Icc a (t 0)`. -/
#check (AffineMap.lipschitzOnWith_chainInterpolation_of_strictAnti :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : NNReal) (a : ℝ) (t : ℕ → ℝ) (x : ℕ → E) (x0 : E) (f : ℝ → E)
    (_ : StrictAnti t) (_ : ∀ n, a < t n)
    (_ : Tendsto t atTop (𝓝 a)) (_ : Tendsto x atTop (𝓝 x0))
    (_ : ∀ n, ‖x (n + 1) - x n‖ ≤ (K : ℝ) * |t (n + 1) - t n|)
    (_ : f a = x0)
    (_ : ∀ n, Set.EqOn f
      (fun s ↦ AffineMap.lineMap (x (n + 1)) (x n)
        ((s - t (n + 1)) / (t n - t (n + 1))))
      (Set.Icc (t (n + 1)) (t n))),
    LipschitzOnWith K f (Set.Icc a (t 0)))
