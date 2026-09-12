# Rockafellar Sum

Lean 4 and mathlib formalization of the S3 Lorentz seed construction on real
`c₀`, with the continuous dual represented by `ℓ¹`.

**Authors:** Junyu Zhang, Zichen Wang, Benqi Liu, and Zaiwen Wen.

## Why This Problem Matters

Many optimization and equilibrium problems can be written as a monotone
inclusion

$$0 \in A(x) + B(x).$$

For example, the constrained convex optimality condition
`0 ∈ ∂f(x) + N_C(x)` combines an objective's subdifferential with the normal
cone of a constraint set. More general monotone operators also describe
variational inequalities and saddle-point systems. Addition is therefore a
basic operation for combining models and separating their computational parts.

The sum of two monotone operators is monotone, but **maximal monotonicity**
is stronger: the graph admits no proper monotone extension. This property
underlies the resolvent theory used in proximal and operator-splitting
methods. In Hilbert space, a maximally monotone operator has an everywhere
defined, single-valued resolvent. Maximality alone does not guarantee that
the operator has a zero, or that a particular splitting algorithm converges.

The classical sum problem asks whether two maximally monotone operators on
a real Banach space remain maximally monotone after addition under the
interior-domain condition

$$\operatorname{dom} A \cap \operatorname{int}(\operatorname{dom} B)
\ne \varnothing.$$

Rockafellar proved this in reflexive Banach spaces. The difficulty is whether
the same condition suffices without reflexivity. This repository studies
that boundary on `c₀`, a standard nonreflexive Banach space. Its construction
uses a normal cone to a ball as one summand, so the obstruction already
arises with a simple convex constraint. The seed-and-extension proof isolates
the mechanism: an origin witness is compatible with every point of the sum
graph but is absent from that graph.

## Research History

| Period | Development |
| --- | --- |
| 1962 | [Minty's work on monotone nonlinear operators in Hilbert space](https://doi.org/10.1215/S0012-7094-62-02933-2) established foundational links between monotonicity and range properties, central to modern resolvent methods. |
| 1970 | [Rockafellar's sum theorem](https://doi.org/10.1090/S0002-9947-1970-0282272-5) established maximality of sums under the interior-domain condition in reflexive Banach spaces. |
| 1970 | [Rockafellar's maximality theorem for subdifferentials](https://doi.org/10.2140/pjm.1970.33.209) established maximal monotonicity for the subdifferential of a proper lower-semicontinuous convex function on a Banach space. This connects the theory to convex optimization and normal cones. |
| 2012 | [Bauschke, Borwein, Wang, and Yao](https://doi.org/10.1007/s11228-012-0209-0) studied pathological maximally monotone operators on nonreflexive Banach spaces, illustrating why conclusions from reflexive spaces require care in the general setting. |
| 2014 | [Borwein and Yao's sum theorems for operators of type (FPV)](https://doi.org/10.1017/S1446788714000056) gave positive results with additional operator and domain structure. Their paper explicitly described the general sum problem as a major open problem. |

These results distinguish the general sum question from special cases with
additional regularity or domain geometry. The present repository provides a
machine-checkable candidate counterexample to the unrestricted Banach-space
extension of the classical interior-domain theorem. The formal result and
its verification scope are recorded below; it does not contradict the
reflexive-space theorem or assert failure of specific numerical algorithms.

### References

1. G. J. Minty, *Monotone (nonlinear) operators in Hilbert space*, Duke
   Mathematical Journal **29** (1962), 341–346.
2. R. T. Rockafellar, *On the maximality of sums of nonlinear monotone
   operators*, Transactions of the American Mathematical Society **149**
   (1970), 75–88.
3. R. T. Rockafellar, *On the maximal monotonicity of subdifferential mappings*,
   Pacific Journal of Mathematics **33** (1970), 209–216.
4. H. H. Bauschke, J. M. Borwein, X. Wang, and L. Yao, *Construction of
   pathological maximally monotone operators on non-reflexive Banach spaces*,
   Set-Valued and Variational Analysis **20** (2012), 387–415.
5. J. M. Borwein and L. Yao, *Sum theorems for maximally monotone operators
   of type (FPV)*, Journal of the Australian Mathematical Society (2014),
   DOI: [10.1017/S1446788714000056](https://doi.org/10.1017/S1446788714000056).

## Requirements

- Lean 4 `v4.32.0`
- mathlib `v4.32.0`

## Main Theorem

```lean
C0Seq.exists_maximalMonotone_sum_not_maximal
```

Two maximally monotone operators satisfy the interior-domain condition, but
their pointwise sum is not maximally monotone:

```lean
∃ A B : SetValuedOperator C0Seq L1Seq,
  Maximal coordinateDualPairing.IsMonotone A.graph ∧
  Maximal coordinateDualPairing.IsMonotone B.graph ∧
  (A.dom ∩ interior B.dom).Nonempty ∧
  ¬ Maximal coordinateDualPairing.IsMonotone (A + B).graph
```

The statement above is written inside `namespace C0Seq`.
The construction theorem `Lorentz.exists_seedCounterexample` constructs a maximally monotone operator
whose sum with the normal cone of the closed radius-12 ball is not maximally
monotone, despite the interior-domain qualification. It uses an explicit
monotone seed and a Zorn maximal extension.

## Entry Points

- [S3.lean](S3.lean): the seed proof and final theorem.
- [ReasLib.lean](ReasLib.lean): complete library import index.
- [rockafellar_sum.lean](rockafellar_sum.lean): project entry point.

## Proof Map

| Stage | Source |
| --- | --- |
| Fixed detectors and polar containment | [SeedSchedule](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedSchedule.lean) |
| Full seed monotonicity and local energy | [SeedAssembly](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedAssembly.lean) |
| Concrete witnesses and maximal extension | [SeedWitnesses](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedWitnesses.lean) |
| Normal-cone sum and final theorem | [SeedCounterexample](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedCounterexample.lean) |

The former S2 wrappers and GhostCurve construction are removed from this branch;
Git history retains the previous proof route. Shared analytic infrastructure remains.

## Verification

Install [elan](https://github.com/leanprover/elan). The project pins Lean and
mathlib v4.32.0; Lake resolves dependencies on the first run. Run checks serially:

```bash
lake lean ReasLib.lean
lake lean S3.lean
lake lean rockafellar_sum.lean
```

[CI](.github/workflows/lean_action_ci.yml) checks these entry points and rejects
proof placeholders. A local kernel audit of the final S3 theorem, seed existence,
and actual polar-carrier theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Comparator verification

The following proof interfaces were checked with
[`leanprover/comparator`](https://github.com/leanprover/comparator) `v4.32.0`
on 12 September 2026, against source commit
[`159d2fb`](https://github.com/imathwy/rockafellar_sum/commit/159d2fb0e9e62cca176592c786cbe1614ef0a1ae).
Comparator compared separately stated Challenge declarations with Solution
wrappers applying the repository theorems, checked the permitted axioms, and
replayed the exported Solution in Lean's default kernel.

| Target | Lean / kernel audit | Comparator status |
| --- | --- | --- |
| `C0Seq.exists_maximalMonotone_sum_not_maximal` | Passed; standard three axioms only | `Your solution is okay!` |
| `Lorentz.exists_seedCounterexample` | Passed; standard three axioms only | `Your solution is okay!` |
| `Lorentz.seedPoint_polar_subset_carrier` | Passed; standard three axioms only | `Your solution is okay!` |

Both runs exited successfully and reported `Lean default kernel accepts the
solution`. The axiom budget was exactly `propext`, `Classical.choice`, and
`Quot.sound`; Nanoda was not enabled. Builds and exports used real landrun
v0.1.17 through a delimiter-only command-line adapter. Temporary wrappers and
build artifacts stayed outside the tracked repository.

This was a trusted-source local verification, run in a root session without
the upstream `systemd-run` AF_UNIX restriction; it does not claim the full
adversarial-isolation guarantees described upstream. Comparator does not
establish correspondence with the manuscript. See the
[verification record](docs/comparator-verification.md) for tool revisions,
configuration and result details.

## Code scale

Measured from the tracked Lean sources on 12 September 2026; physical lines
include comments and blank lines. Caches and local manuscripts are excluded.

| Metric | Value |
| --- | ---: |
| Lean source files | 64 |
| Physical Lean lines | 6,552 |
| `ReasLib` modules, excluding its aggregate | 61 |

Formal verification establishes the stated Lean propositions. Independent
source-to-formalization review remains important for the candidate counterexample.
Manuscript snapshots, scripts, runtime state, caches and local coordination
notes are excluded from commits.
