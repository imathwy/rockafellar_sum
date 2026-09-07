module

public import ReasLib.Analysis.C0Seq.NormalCone
public import S2.Final.fixedBall_normalCone_polar_subset_Pairing

public section

open scoped Pointwise

/- Lemma 7.14a (At zero the normal-cone contribution vanishes): if `(0, 0)` lies
in the graph of the sum with the normal cone of `C0Seq.finalConstraint`, then its
normal-cone summand is zero and `(0, 0)` lies in the graph of `M`. -/
#check (C0Seq.zero_mem_graph_of_mem_add_normalCone C0Seq.dualPairing :
  ∀ M : SetValuedOperator C0Seq L1Seq,
    (0, 0) ∈ (M + C0Seq.dualPairing.normalCone C0Seq.finalConstraint).graph →
      (0, 0) ∈ M.graph)
