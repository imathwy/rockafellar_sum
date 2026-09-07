/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.C0Seq.NormalCone
public import S2.Final.fixedBall_normalCone_polar_subset_Pairing

/-!
# Origin membership in a normal-cone sum graph

This module reduces origin membership in an operator plus fixed-ball normal cone
to origin membership in the original operator graph.
-/

public section

open scoped Pointwise

/- Lemma 7.14a (At zero the normal-cone contribution vanishes): if `(0, 0)` lies
in the graph of the sum with the normal cone of `C0Seq.finalConstraint`, then its
normal-cone summand is zero and `(0, 0)` lies in the graph of `M`. -/
#check (C0Seq.zero_mem_graph_of_mem_add_normalCone C0Seq.dualPairing :
  ∀ M : SetValuedOperator C0Seq L1Seq,
    (0, 0) ∈ (M + C0Seq.dualPairing.normalCone C0Seq.finalConstraint).graph →
      (0, 0) ∈ M.graph)
