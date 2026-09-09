# Rockafellar Sum Counterexample

Lean 4 and mathlib formalization of the S3 Lorentz seed construction on real
`c₀`, with the continuous dual represented by `ℓ¹`.

`Lorentz.exists_seedCounterexample` constructs a maximally monotone operator
whose sum with the normal cone of the closed radius-12 ball is not maximally
monotone, despite the interior-domain qualification. It uses an explicit
monotone seed and a Zorn maximal extension.

## Entry Points

- `S3.lean`: the seed proof and final theorem.
- `ReasLib.lean`: the reusable library aggregate.
- `rockafellar_sum.lean`: the project aggregate.
- `ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/SeedCounterexample.lean`:
  final normal-cone argument.
- `SeedSchedule.lean` in the same directory: actual detector points, monotonicity,
  and polar-carrier containment.
- `SeedWitnesses.lean`: concrete witnesses and unconditional seed existence.

The former S2 wrappers and GhostCurve construction are removed from this branch;
Git history retains the previous proof route. Shared analytic infrastructure remains.

## Verification

The project pins Lean and mathlib v4.32.0. Run checks serially:

```bash
lake lean ReasLib.lean
lake lean S3.lean
lake lean rockafellar_sum.lean
```

CI checks these entry points and rejects proof placeholders. Comparator owns
separate declaration-identity checks; the removed CI audit tools are not restored.
A local kernel audit of the final S3 theorem, seed existence, and actual
polar-carrier theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

Formal verification establishes the stated Lean propositions. Independent
source-to-formalization review remains important for the candidate counterexample.
Manuscript snapshots, scripts, runtime state, caches and local coordination
notes are excluded from commits.
