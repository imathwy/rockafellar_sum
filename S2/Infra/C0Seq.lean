/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0

/-!
# The real `C0Seq` model

This source-facing module records the canonical real sequence space tending to
zero.
-/

public section

/- Infrastructure A.1 (The c₀ sequence model): the real sequence space `c₀`, modeled as
continuous maps on the discrete space `ℕ` that vanish at infinity. -/
#check (C0Seq : Type)
