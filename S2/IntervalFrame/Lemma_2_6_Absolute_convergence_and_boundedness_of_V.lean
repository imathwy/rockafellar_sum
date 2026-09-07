/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import S2.IntervalFrame.Definition_2_5_The_interval_coordinate_operator_V_Operator

/-!
# Absolute convergence and boundedness of `V`

This source-facing module records the convergence and operator-norm bounds for
the interval-coordinate synthesis.
-/

/- Lemma 2.6 (Absolute convergence and boundedness of $V$) (1):
the series defining `intervalCoordinateOperator a` and its absolute convergence. -/
#check L1Seq.intervalCoordinateOperator_apply
#check L1Seq.summable_norm_smul_rationalIntervalVec

/- Lemma 2.6 (Absolute convergence and boundedness of $V$) (2):
the pointwise estimate `‖intervalCoordinateOperator a‖ ≤ ‖a‖`. -/
#check L1Seq.norm_intervalCoordinateOperator_apply_le

/- Lemma 2.6 (Absolute convergence and boundedness of $V$) (3):
the bundled bounded linear operator and its norm estimate. -/
#check L1Seq.intervalCoordinateOperator
#check L1Seq.norm_intervalCoordinateOperator_le
