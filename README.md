# Rockafellar Sum

Lean 4 and mathlib formalization of a counterexample to the Banach-space
extension of Rockafellar's sum theorem. The construction takes place on real
`c₀`, with its continuous dual represented by `ℓ¹`.

**Authors:** Junyu Zhang, Zichen Wang, Benqi Liu, and Zaiwen Wen.

[Main theorem](#main-theorem) · [Quick start](#quick-start) ·
[Research history](#research-history) · [Comparator verification](#comparator-verification)

## Main theorem

There exist maximally monotone operators `A` and `B` satisfying the
interior-domain condition such that `A + B` is not maximally monotone.

The exported declaration is
[`C0Seq.exists_maximalMonotone_sum_not_maximal`](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedCounterexample.lean).
Its proposition, written inside `namespace C0Seq`, is:

```lean
∃ A B : SetValuedOperator C0Seq L1Seq,
  Maximal coordinateDualPairing.IsMonotone A.graph ∧
  Maximal coordinateDualPairing.IsMonotone B.graph ∧
  (A.dom ∩ interior B.dom).Nonempty ∧
  ¬ Maximal coordinateDualPairing.IsMonotone (A + B).graph
```

The more specific theorem `Lorentz.exists_seedCounterexample` takes `B`
to be the normal cone of the closed radius-12 ball. An explicit monotone
seed is extended by Zorn's lemma; the origin witnesses failure of maximality
for the sum.

## Quick start

Install [elan](https://github.com/leanprover/elan), then clone the repository
with an account that has access:

```sh
git clone https://github.com/imathwy/rockafellar_sum.git
cd rockafellar_sum
lake lean S3.lean
```

[lean-toolchain](lean-toolchain) pins Lean **v4.32.0**.
[lakefile.toml](lakefile.toml) pins mathlib **v4.32.0**, with resolved
dependencies in [lake-manifest.json](lake-manifest.json). The first check
may download and compile dependencies.

To inspect the result in a Lean file in this project:

```lean
import S3

#check C0Seq.exists_maximalMonotone_sum_not_maximal
#check Lorentz.exists_seedCounterexample
```

The complete entry-point checks are:

```sh
lake lean ReasLib.lean
lake lean S3.lean
lake lean rockafellar_sum.lean
```

Run these serially when sharing a Lake cache.
[CI](.github/workflows/lean_action_ci.yml) runs the same three checks and
rejects proof placeholders.

## Why the problem matters

Monotone inclusions provide a common language for optimization, variational
inequalities, and equilibrium problems:

$$0 \in A(x)+B(x).$$

For a proper lower-semicontinuous convex objective and a closed convex
constraint set, the inclusion $0\in\partial f(x)+N_C(x)$ expresses
constrained optimality under an appropriate subdifferential sum-rule
qualification. Splitting the two operators separates the objective from
the constraint.

The sum of monotone operators is monotone. The harder question is whether
it is **maximally monotone**: its graph admits no proper monotone extension.
Maximality underpins resolvent methods. In a real Hilbert space, the
resolvent $(I+\lambda A)^{-1}$ of a maximally monotone operator is
everywhere defined and single-valued for $\lambda>0$.

Rockafellar's classical sum theorem assumes reflexivity and the condition

$$\operatorname{dom}A\cap\operatorname{int}(\operatorname{dom}B)
\ne\varnothing.$$

The general sum problem asks whether this condition suffices in an arbitrary
real Banach space. The space `c₀` tests the nonreflexive boundary. Here one
summand is the normal cone of a ball, while the other comes from a monotone
seed. The construction isolates how a simple constraint can leave a point
in the sum's monotone polar but outside its graph.

## Research history

These selected milestones distinguish the classical reflexive-space theorem
from later results requiring additional structure.

- **1962 — Hilbert-space foundations.** G. J. Minty's
  [*Monotone (nonlinear) operators in Hilbert space*](https://doi.org/10.1215/S0012-7094-62-02933-2),
  Duke Mathematical Journal **29**, 341–346, developed the range theory
  underlying the resolvent approach.
- **1970 — The sum theorem.** R. T. Rockafellar's
  [*On the maximality of sums of nonlinear monotone operators*](https://doi.org/10.1090/S0002-9947-1970-0282272-5),
  Transactions of the American Mathematical Society **149**, 75–88,
  established maximality of sums under the interior-domain condition in
  reflexive Banach spaces.
- **1970 — Convex subdifferentials.** Rockafellar's
  [*On the maximal monotonicity of subdifferential mappings*](https://doi.org/10.2140/pjm.1970.33.209),
  Pacific Journal of Mathematics **33**, 209–216, established maximal
  monotonicity of subdifferentials of proper lower-semicontinuous convex
  functions on Banach spaces, including normal cones as a special case.
- **2012 — Nonreflexive examples.** H. H. Bauschke, J. M. Borwein,
  X. Wang, and L. Yao's
  [*Construction of pathological maximally monotone operators on non-reflexive Banach spaces*](https://doi.org/10.1007/s11228-012-0209-0),
  Set-Valued and Variational Analysis **20**, 387–415, investigated
  phenomena that distinguish nonreflexive monotone operator theory.
- **2014 — Positive results for type (FPV).** J. M. Borwein and L. Yao's
  [*Sum theorems for maximally monotone operators of type (FPV)*](https://doi.org/10.1017/S1446788714000056),
  Journal of the Australian Mathematical Society **97**(1), 1–26,
  proved sum results with additional operator and domain hypotheses.
  Their paper described the general sum problem as a major open problem.

The result formalized here addresses the extension beyond reflexive spaces.
The correspondence between the manuscript and the formal definitions is
reviewed separately from kernel acceptance, as described below.

## Proof organization

The seed route avoids constructing an entire maximal graph explicitly.
Detector points force its monotone polar into a Lorentz carrier; coordinate
bounds give local nonnegative energy; Zorn supplies a maximal extension.

| Stage | Source |
| --- | --- |
| Fixed detectors and polar containment | [SeedSchedule](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedSchedule.lean) |
| Seed monotonicity and local energy | [SeedAssembly](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedAssembly.lean) |
| Concrete witnesses and maximal extension | [SeedWitnesses](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedWitnesses.lean) |
| Normal-cone sum and final theorem | [SeedCounterexample](ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedCounterexample.lean) |

[S3.lean](S3.lean) imports the proof, [ReasLib.lean](ReasLib.lean) indexes the
library, and [rockafellar_sum.lean](rockafellar_sum.lean) is the project entry.
Local manuscripts, working notes, scripts, and generated caches are ignored.

## Comparator verification

Three interfaces passed
[`leanprover/comparator`](https://github.com/leanprover/comparator)
**v4.32.0** on **12 September 2026**, against source commit
[`159d2fb`](https://github.com/imathwy/rockafellar_sum/commit/159d2fb0e9e62cca176592c786cbe1614ef0a1ae).

| Exported theorem checked through a Solution wrapper | Result |
| --- | --- |
| `C0Seq.exists_maximalMonotone_sum_not_maximal` | `Your solution is okay!` |
| `Lorentz.exists_seedCounterexample` | `Your solution is okay!` |
| `Lorentz.seedPoint_polar_subset_carrier` | `Your solution is okay!` |

The two runs checked Challenge/Solution declaration identity and the axiom
budget, replayed the exported solutions in Lean's default kernel, and
exited with code 0. The permitted axioms were exactly `propext`,
`Classical.choice`, and `Quot.sound`; Nanoda was not enabled.

This was a trusted-source local check using real landrun v0.1.17. It ran
as root without the additional upstream AF_UNIX restriction, so it does
not carry the full hostile-submission isolation guarantee. Comparator
checks the formal interfaces; it does not certify their correspondence
with the manuscript. The [verification record](docs/comparator-verification.md)
documents the wrappers, tool revisions, configuration, and execution boundary.

## Code scale

Measured from tracked Lean sources on 12 September 2026. Physical lines
include comments and blank lines; caches and local manuscripts are excluded.

| Metric | Value |
| --- | ---: |
| Lean source files | 64 |
| Physical Lean lines | 6,552 |
| `ReasLib` modules, excluding its aggregate | 61 |
