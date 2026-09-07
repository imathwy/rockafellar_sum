/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.InnerProductSpace.HilbertProd2

/-!
# Two-coordinate Hilbert products

This source-facing module records the canonical product type, projections, and
Euclidean formulas used for Lorentz coordinates.
-/

@[expose] public section

open scoped InnerProductSpace

universe u

/- Infrastructure A.14 (The Hilbert ℓ²-product model): the fixed model is
`WithLp 2 (H × ℝ)`, with its canonical coordinates and Euclidean formulas. -/
#check (HilbertProd2 : Type u → Type u)

#check (HilbertProd2.mk : {H : Type u} → H → ℝ → HilbertProd2 H)

#check (HilbertProd2.fst : {H : Type u} → HilbertProd2 H → H)

#check (HilbertProd2.snd : {H : Type u} → HilbertProd2 H → ℝ)

#check (HilbertProd2.fst_mk :
  ∀ {H : Type u} (v : H) (r : ℝ), HilbertProd2.fst (HilbertProd2.mk v r) = v)

#check (HilbertProd2.snd_mk :
  ∀ {H : Type u} (v : H) (r : ℝ), HilbertProd2.snd (HilbertProd2.mk v r) = r)

#check (HilbertProd2.mk_fst_snd :
  ∀ {H : Type u} (x : HilbertProd2 H),
    HilbertProd2.mk (HilbertProd2.fst x) (HilbertProd2.snd x) = x)

#check (HilbertProd2.ext :
  ∀ {H : Type u} {x y : HilbertProd2 H},
    HilbertProd2.fst x = HilbertProd2.fst y →
      HilbertProd2.snd x = HilbertProd2.snd y → x = y)

#check (HilbertProd2.norm_mk_sq :
  ∀ {H : Type u} [NormedAddCommGroup H] (v : H) (r : ℝ),
    ‖WithLp.toLp 2 (v, r)‖ ^ 2 = ‖v‖ ^ 2 + r ^ 2)

#check (HilbertProd2.inner_mk :
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v w : H) (r s : ℝ),
    ⟪WithLp.toLp 2 (v, r), WithLp.toLp 2 (w, s)⟫_ℝ = ⟪v, w⟫_ℝ + r * s)
