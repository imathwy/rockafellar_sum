# Rockafellar Sum Counterexample

Lean 4 and mathlib formalization of the interval-indicator construction and
the Rockafellar-style maximal-monotonicity candidate counterexample on real
`c₀` developed from an internal candidate-proof manuscript.

The formalization constructs a maximally monotone operator `M`, takes the
normal cone of the closed radius-`1 / 2` ball, verifies the interior-domain
constraint qualification, and proves that the pointwise sum is not maximally
monotone. The manuscript concerns a long-standing open problem, so the result
remains a candidate counterexample pending independent mathematical review.

## Toolchain

- Lean `v4.32.0` (`lean-toolchain`)
- Mathlib `v4.32.0` (`lakefile.toml`)

## Repository layout

- `ReasLib/`: reusable definitions, constructions, and proof owners.
- `S2/`: source-facing, labeled declarations and canonical `#check` entries.
- `ReasLib.lean`, `S2.lean`: complete aggregate entry points.
- `rockafellar_sum.lean`: project entry point importing both aggregates.

M2F runtime state, editor configuration, scratch probes, manuscript sources,
generated TeX files, and local progress documents are intentionally excluded
from version control.

## Verification

Run a single target with the lightweight checker:

```bash
lake lean ReasLib/FunctionalAnalysis/SequenceSpace/RationalTimeOperator/Parametrization/GhostCurve/Maximal.lean
```

Check the three project entry points:

```bash
lake lean ReasLib.lean
lake lean S2.lean
lake lean rockafellar_sum.lean
```

The GitHub Actions workflow runs the three project entry points and rejects new
proof placeholders in the production Lean sources. Trusted-axiom and
declaration-identity checks are supplied separately by the Comparator workflow
maintained for this project; no generated axiom-audit source is checked in.

The current source snapshot contains 152 `ReasLib` modules and 237 `S2`
modules. It has no actual `sorry`, `admit`, project-defined `axiom`, or
`sorryAx` in production source. A declaration-level audit of 1053 exported
project declarations accepts only `propext`, `Classical.choice`, and
`Quot.sound`.

These checks are formalization gates, not an independent certification of the
mathematics in the manuscript. The result should still be described as a
candidate proof/counterexample until the semantic and TeX review is complete.
The default worker image has no installed TeX engine. A temporary Tectonic
baseline has generated the manuscript successfully, but publication layout
warnings and independent semantic review remain open.
