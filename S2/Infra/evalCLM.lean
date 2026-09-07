module

public import ReasLib.FunctionalAnalysis.SequenceSpace.C0.Coordinate

public section

/- Infrastructure A.3 (Coordinate evaluation and the c₀ sup norm) (1): evaluation at every
coordinate is a continuous real-linear functional on `C0Seq`. -/
#check (C0Seq.evalCLM : (n : ℕ) → C0Seq →L[ℝ] ℝ)

#check (C0Seq.continuous_apply :
  (n : ℕ) → Continuous (fun x : C0Seq ↦ x n))

#check (C0Seq.evalCLM_apply :
  (n : ℕ) → (x : C0Seq) → C0Seq.evalCLM n x = x n)

/- Infrastructure A.3 (Coordinate evaluation and the c₀ sup norm) (2): every coordinate is
bounded in absolute value by the `C0Seq` norm. -/
#check (C0Seq.abs_apply_le_norm :
  (x : C0Seq) → (n : ℕ) → |x n| ≤ ‖x‖)

/- Infrastructure A.3 (Coordinate evaluation and the c₀ sup norm) (3): the `C0Seq` norm is the
supremum of the absolute values of its coordinates in the bounded-function representation. -/
#check (C0Seq.norm_eq_iSup_abs :
  (x : C0Seq) → ‖x‖ = ⨆ n : ℕ, |x n|)
