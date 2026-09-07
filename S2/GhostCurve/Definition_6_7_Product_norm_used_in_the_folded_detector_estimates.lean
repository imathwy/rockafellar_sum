/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

import S2.Infra.zSize

/-!
# Product Norm for Folded Estimates

This module exposes the coordinate-sum product norm used in folded estimates.
-/

/- Definition 6.7 (Product norm used in the folded detector estimates):
on `C0Seq × L1Seq`, use the coordinate-sum size, equivalently the canonical
`WithLp 1` product norm. -/
#check C0Seq.zSize
#check C0Seq.zSize_apply
#check C0Seq.zSize_eq_norm_toLp
