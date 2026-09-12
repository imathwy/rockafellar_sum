# Rockafellar Sum

Lean 4 and mathlib formalization of the S3 Lorentz seed construction on real
`c₀`, with the continuous dual represented by `ℓ¹`.

**Authors:** Junyu Zhang, Zichen Wang, Benqi Liu, and Zaiwen Wen.

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

Independent declaration verification is tracked separately using
[`leanprover/comparator`](https://github.com/leanprover/comparator). Comparator
checks Challenge/Solution declaration identity, kernel acceptance, and the
configured axiom budget. The intended release is `v4.32.0`, matching this
repository's Lean toolchain.

| Target | Lean / kernel audit | Comparator status |
| --- | --- | --- |
| `C0Seq.exists_maximalMonotone_sum_not_maximal` | Passed; standard three axioms only | Pending |
| `Lorentz.exists_seedCounterexample` | Passed; standard three axioms only | Pending |
| `Lorentz.seedPoint_polar_subset_carrier` | Passed; standard three axioms only | Pending |

No completed Comparator Challenge/Solution run is recorded for this version.
The Lean checks above are not a substitute for that verification. Successful
Comparator results will be recorded against the exact checked commit when
available. Comparator does not establish correspondence between the formal
definitions and the manuscript; that is a separate semantic review.

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
