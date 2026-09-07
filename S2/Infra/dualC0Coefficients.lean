/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Dual

/-!
# Dual coefficients of c0

This module records the l1 coefficient representation of continuous functionals on C0Seq.
-/

public section

/- Infrastructure A.10 (Coordinate representation of a functional on c₀): the coefficient
sequence of a continuous functional on `C0Seq`. -/
#check (C0Seq.dualCoefficients : StrongDual ℝ C0Seq → L1Seq)

#check (C0Seq.dualCoefficients_memℓp :
  ∀ φ : StrongDual ℝ C0Seq,
    Memℓp (fun n : ℕ ↦ φ (c0Single n 1)) 1)

#check (C0Seq.dualCoefficients_apply :
  ∀ (φ : StrongDual ℝ C0Seq) (n : ℕ),
    C0Seq.dualCoefficients φ n = φ (c0Single n 1))

#check (C0Seq.norm_dualCoefficients_le :
  ∀ φ : StrongDual ℝ C0Seq, ‖C0Seq.dualCoefficients φ‖ ≤ ‖φ‖)

#check (C0Seq.apply_eq_tsum_dualCoefficients :
  ∀ (φ : StrongDual ℝ C0Seq) (x : C0Seq),
    φ x = ∑' n : ℕ, x n * C0Seq.dualCoefficients φ n)
