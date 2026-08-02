# Algorithmic Randomness

[![Lean CI](https://github.com/cameronfreer/algorithmic-randomness/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/algorithmic-randomness/actions/workflows/lean_action_ci.yml)

A Lean 4 library for algorithmic randomness on fair-coin Cantor space, built on
[mathlib](https://github.com/leanprover-community/mathlib4).

The library develops computability and measure theory together: effective objects are
represented by **actual program codes**, equipped with executable finite approximations and
correctness theorems connecting them to their set- and measure-theoretic denotations.

## Highlights

- Cantor-space cylinders and fair-coin measure, with exact dyadic calculations for finite
  unions of cylinders.
- Coded uniformly c.e. open sets with canonical increasing finite-stage approximations.
- Martin-Löf and Schnorr tests, including a coded universal Martin-Löf test.
- Conullity of Martin-Löf randomness, and non-randomness of computable points.
- Rational tree martingales, Ville's inequality, computable randomness, and the implication
  from Martin-Löf randomness to computable randomness.

## Architecture

The central interface is

```text
program code → finite stages → semantic open set → measure/randomness theorem
```

Codes and their denotations remain separate. Executable constructions use concrete `Nat`- and
`List`-based representations; correctness lemmas connect them to exact rational weights, sets,
and measures. Uniform constructions produce genuine program codes rather than only functions
accompanied by abstract computability predicates.

See [docs/architecture.md](docs/architecture.md) for the design decisions behind this and why
they are load-bearing.

The source is organized by mathematical layer:

| Directory | Contents |
| --- | --- |
| `Cantor/` | Cantor space, cylinders, fair-coin measure, finite open sets |
| `Coding/` | Program codes and executable numeric and finite-open representations |
| `EffectiveOpen/` | Coded c.e. open families, reindexing, and trimming |
| `Randomness/` | Martin-Löf and Schnorr tests, and randomness implications |
| `Martingale/` | Tree martingales, Ville's inequality, and computable martingales |

## Using the library

Import the complete public library with:

```lean
import AlgorithmicRandomness
```

Individual modules may be imported directly when narrower dependencies are preferred. Public
declarations live in the `AlgorithmicRandomness` namespace.

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```
lake exe cache get
lake build
```

The Lean toolchain and the complete dependency graph are pinned in `lean-toolchain` and
`lake-manifest.json`.

## Development

The main `AlgorithmicRandomness` library is the stable dependency spine. Work in progress is
isolated in `AlgorithmicRandomnessExperimental`, which may not be imported by the main library.
CI builds both targets and enforces the dependency boundary.

## License

Apache 2.0 — see [LICENSE](LICENSE).
