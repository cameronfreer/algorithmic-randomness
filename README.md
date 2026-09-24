# Algorithmic Randomness

[![Lean CI](https://github.com/cameronfreer/algorithmic-randomness/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/algorithmic-randomness/actions/workflows/lean_action_ci.yml)

A Lean 4 library for algorithmic randomness on fair-coin Cantor space, built on
[mathlib](https://github.com/leanprover-community/mathlib4).

The library develops computability and measure theory together: effective objects are
represented by **actual program codes**, equipped with primitive recursive finite approximations
and correctness theorems connecting them to their set- and measure-theoretic denotations. Where an
approximation is built over an extracted code it is `Primrec` as a function without reducing in
the kernel; where it is built from concrete data it also runs, and compile-time checks exercise
it.

## Status

The project is under active development and does not yet promise API stability.
`AlgorithmicRandomness` is the public dependency spine; work in progress is isolated in
`AlgorithmicRandomnessExperimental`.

Established implications among randomness notions:

| From | To | Route |
| --- | --- | --- |
| Martin-Löf random | computably random | Ville's inequality on a coded threshold test |
| computably random | Schnorr random | simulation of the conditional-probability martingale |
| Martin-Löf random | Schnorr random | structural, and also by composition |
| Schnorr random | Kurtz random | the Schnorr test a null computable tree already carries |
| computably random | Kurtz random | by composition |
| Martin-Löf random | Kurtz random | by composition |

No computable point is random in any of these senses. Martin-Löf, Schnorr, and Kurtz randomness
each have their own witness — for Kurtz randomness the prefix tree of the point, since the weakest
notion cannot inherit the argument from the stronger ones — and computable randomness then follows
from the Kurtz case through the hierarchy.

## Characterizations and analytic witnesses

### Levin–Schnorr

Martin-Löf randomness is incompressibility of initial segments:

```lean
IsMartinLofRandom x ↔ ∃ c, ∀ n, n ≤ prefixComplexity (initSeg x n) + c
```

`prefixComplexity τ` is the length of a shortest description of `τ` under an optimal universal
prefix-free machine, which the library constructs as one actual program code rather than
postulating. The additive constant absorbs the choice of description machine: any prefix-free
machine is simulated by the universal one with bounded overhead, so a different choice shifts `c`
and nothing else.

The statement is deliberately subtraction-free. Phrasing the bound with `n - c` on the left would
introduce truncated natural subtraction and make the small-`n` cases hold for the wrong reason.

Both directions are proved. See
[docs/prefix-free-machines.md](docs/prefix-free-machines.md) for how the two constructions behind
them fit together.

### Computable randomness and differentiability

Computable randomness of a real in the unit interval is characterized by differentiability, in
two presentations of computable functions:

```lean
theorem isComputablyRandomReal_iff_forall_computableMonotone (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    IsComputablyRandomReal z ↔ ∀ g : ComputableMonotone, DifferentiableAt ℝ g.toFun z

theorem isComputablyRandomReal_iff_forall_computableLipschitz (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    IsComputablyRandomReal z ↔ ∀ f : ComputableLipschitz, DifferentiableAt ℝ f.toFun z
```

The first is the theorem of Brattka–Miller–Nies
([arXiv:1104.4465](https://arxiv.org/abs/1104.4465)); the second is Freer–Kjos-Hanssen–Nies–Stephan
([arXiv:1402.2429](https://arxiv.org/abs/1402.2429), Theorem 4.2). Each is a statement about a
specific presentation and should be read against it:

- a *computable nondecreasing function* (`ComputableMonotone`) is a continuous nondecreasing
  function on `[0, 1]` together with a program approximating its value at any rational argument
  to within `2⁻ᵏ`;
- a *computable Lipschitz function* (`ComputableLipschitz`) is a function on `[0, 1]` with a
  natural Lipschitz bound, together with a program computing its exact rational values at the
  dyadic cut points.

Both are extended to `ℝ` by clamping. The unit-interval hypothesis cannot be dropped: outside
`[0, 1]` every such extension is locally constant, so universal differentiability holds there,
while no real outside `[0, 1]` is computably random.

The substantial direction is that at a computably random real every computable nondecreasing
function is differentiable. It follows BMN. Chord slopes over the cells of a rationally scaled and
shifted dyadic grid form a computable martingale, so at a computably random real every computable
nondecreasing function has bounded chord slopes nearby. If differentiability failed, two
separated chord slopes would recur at arbitrarily small scales. A finite family of such grids
captures them, and an interpolation construction turns them into a second computable
nondecreasing function whose chord slopes near the point are unbounded, which is a contradiction.

The Lipschitz characterization then needs no further construction. Adding `K · x` turns a
computable Lipschitz function into a computable nondecreasing one without affecting
differentiability in the interior. Conversely, a computable martingale succeeding on an expansion
of a non-random `z` yields a computable Lipschitz function whose chord slopes across the prefix
intervals of `z` are exactly the capital of a bounded oscillating martingale, so it is not
differentiable at `z`. That direction also holds in sequence form over Cantor space.

## Verification

CI enforces all of the following on every push:

- the public spine builds with warnings as errors, and the experimental library must typecheck
  under the same linter set;
- the public spine contains no `sorry`, and never imports the experimental library, checked
  against comment- and string-stripped sources so neither can hide in a comment;
- every declaration in the public import spine depends only on the standard axioms `propext`,
  `Classical.choice`, and `Quot.sound`, checked by an environment sweep rather than a curated
  list.

Key executable definitions additionally carry compile-time evaluation checks, so the executable
layer is exercised rather than merely typechecked.

## Highlights

- Cantor-space cylinders and fair-coin measure, with exact dyadic calculations for finite
  unions of cylinders.
- Coded uniformly c.e. open sets with canonical increasing finite-stage approximations.
- Martin-Löf and Schnorr tests, including a coded universal Martin-Löf test.
- Conullity of Martin-Löf randomness, and non-randomness of computable points.
- Rational tree martingales, Ville's inequality, and computable randomness.
- The randomness hierarchy: Martin-Löf random implies computably random implies Schnorr
  random, the second by simulating a computable-real martingale with an exactly rational one.
- Savings normalization, and an oscillating martingale whose capital stays in `[1, 4]` while
  hitting exactly `3` and exactly `2` arbitrarily late along any path where the source succeeds.
- The cumulative function of a tree martingale, built directly at dyadic endpoints, whose chord
  slope across a cylinder is *exactly* the capital there.
- Computable Lipschitz functions with exact rational values at dyadic points, and computable
  nondecreasing functions with rational approximation programs.
- Both characterizations of computable randomness by differentiability, including BMN's
  finite family of affine dyadic grids and its oscillating construction.
- Binary expansions of reals, with `realOf` surjective onto the unit interval.
- Prefix-free machines as coded objects, an optimal universal machine built as one actual program,
  prefix complexity with primitive recursive finite approximations, and Kraft–Chaitin allocation.
- Computable trees and effectively closed classes, with a null path class converted into a Schnorr
  test by searching for thin levels, giving Kurtz randomness at the bottom of the hierarchy.

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
they are load-bearing, and [docs/prefix-free-machines.md](docs/prefix-free-machines.md) for how a
prefix-free machine is represented and the three ways one is built.

The source is organized by mathematical layer:

| Directory | Contents |
| --- | --- |
| `Cantor/` | Cantor space, cylinders, fair-coin measure, finite open sets |
| `Coding/` | Program codes and executable numeric and finite-open representations |
| `EffectiveOpen/` | Coded c.e. open families, reindexing, and trimming |
| `Randomness/` | Martin-Löf, Schnorr, and Kurtz randomness, and the implications among them |
| `Martingale/` | Tree martingales, Ville's inequality, computable and savings martingales |
| `Analysis/` | Dyadic intervals, cumulative functions, computable Lipschitz and nondecreasing functions, differentiability |
| `Complexity/` | Prefix-free machines, the universal machine, Kraft–Chaitin allocation |
| `EffectiveClosed/` | Computable trees, level fronts, and the tests their null path classes carry |

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

## License

Apache 2.0 — see [LICENSE](LICENSE).
