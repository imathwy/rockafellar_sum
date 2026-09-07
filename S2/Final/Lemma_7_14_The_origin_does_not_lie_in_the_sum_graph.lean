module

public import S2.Final.Definition_7_1_The_ghost_curve_operator_M_Operator
import S2.Final.Lemma_7_7_The_origin_is_not_on_the_graph_of_M
public import S2.Final.zero_mem_sumGraph_imp_zero_mem_M
public import S2.Infra.monotone_iff_subset_polar_Monotone
public import ReasLib.Analysis.C0Seq.NormalCone.Origin

public section

open scoped Pointwise

namespace Lorentz

variable (d : C0Seq) (hd : d ≠ 0)
  (h_missing : d ∉ Set.range L1Seq.positiveOperator)
  (zLeft z₀ : parametrizedSubspace d)
  (h : ∀ p q : ℕ, p < q → ℕ → parametrizedSubspace d)
  (h_tendsto : ∀ p q (h_pq : p < q),
    Filter.Tendsto (fun n ↦ negativeCoordinate d hd (h p q h_pq n))
      Filter.atTop (nhds 0))
  (v : parametrizedSubspace d)

/- Lemma 7.14 (The origin does not lie in the sum graph)
The origin is not on the graph of the ghost-curve operator plus the normal cone
of `C0Seq.finalConstraint`. -/
#check (C0Seq.zero_not_mem_add_normalCone_graph_of_quadraticPairing_neg
    (M := ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v)
    (z := (z₀ : C0Seq × L1Seq)) :
  (z₀ : C0Seq × L1Seq) ∈
      (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph →
    C0Seq.quadraticPairing z₀ < 0 →
      C0Seq.coordinateDualPairing.IsMonotone
          (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v).graph →
        (0, 0) ∉
          (ghostCurveOperator d hd h_missing zLeft z₀ h h_tendsto v +
            C0Seq.dualPairing.normalCone C0Seq.finalConstraint).graph)

end Lorentz
