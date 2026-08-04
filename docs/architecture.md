# Architecture

These are the design decisions the library is built on, and the reasons they are load-bearing
rather than stylistic. Each was arrived at because the alternative failed on a concrete
obstruction, noted below.

## Codes and denotations are separate

An effective object is a program code together with theorems about what it denotes. The code
layer and the semantic layer never collapse into one another, and codes are never quotiented by
extensional equality.

A Lean function carrying a `Computable` proof is adequate for an isolated theorem, but not for
uniform constructions. Enumerating all candidate tests, absorbing an arbitrary test into a
universal one, and transforming one program into another all require an *index* to manipulate.
The universal Martin-Löf test is the sharpest case: its defining property is that a single code
absorbs every test, so exhibiting it as a semantic union over indices would prove a theorem
while leaving the construction unmade. Its countable-union description is therefore a *derived*
theorem about one code, not a definition.

## Uniformity is stated, not assumed

Computability results are proved uniformly in every parameter a downstream construction will
vary, and pointwise instances are derived as corollaries.

A theorem of the form `∀ c, Partrec (f c)` is strictly weaker than `Partrec (fun z ↦ f z.1 z.2)`
and does not support a construction that extracts `c` from its own input. Where a later
construction dispatches on a code drawn from its input — as the universal test does, and as
threshold enumeration does — the uniform statement is the one that is actually needed.

## Executable and semantic representations are distinct

Code-producing algorithms use primitive recursive presentations, principally `Nat` and `List`.
`Finset`, `ℚ≥0`, `ℝ≥0`, and measures appear only in correctness statements.

This is forced by the ambient library rather than chosen: the pinned mathlib revision supplies
no `Primcodable (Finset α)` and no `Primcodable ℚ≥0`, so an algorithm written over those types
cannot be proved `Partrec` compositionally and therefore cannot be turned into a code. The
pattern throughout is a pair — a semantic definition and an executable one — joined by a bridge
lemma, with all downstream computability going through the executable side and all downstream
mathematics through the semantic side.

Two recurring consequences:

- Exact rational arithmetic is carried as coded numerators and denominators, with comparison
  decided in `ℕ` by cross-multiplication. This is what allows a threshold test to run *inside* a
  program.
- Filtering and bounded quantification are written as folds, because mathlib's primitive
  recursive list-filter and bounded quantifiers are not parameterized in a second argument.

## Approximation before exactness

A coded c.e. open set is presented through cumulative finite stages with exact dyadic measures,
so that every such set arrives with a canonical increasing lower approximation. Semantic
measure bounds and uniform finite-stage bounds are interchangeable, and both directions are
used: measure bounds yield stage bounds, and constructions that enforce stage bounds recover
the measure bound.

Trimming is the construction this exists to support. It forces an arbitrary coded family to
respect a dyadic budget by greedily accepting cylinders along an append-only chronology,
truncating what does not fit and leaving compliant families untouched. That combination —
every candidate made legal, genuine tests unchanged — is what makes a universal test possible.

## Exact rational capital, and simulation across the gap

Martingales in this library carry exact rational capital, because a betting strategy must be
runnable and later constructions compare its value against coded thresholds. But the martingales
that arise from measure theory are not rational-valued: the conditional-probability martingale
of a test, `2^|σ| · μ(Uₙ ∩ [σ])`, is a computable *real*. Bridging that gap is a construction,
not a translation, and two things had to be established before it could be built.

**Fixed finite stages do not work.** The obvious repair — read each level of the test at one
scheduled finite stage, so every measure involved is an exact dyadic rational — fails for a
reason worth recording. A test's modulus bounds the *measure* of the not-yet-enumerated part of
a level, but says nothing about *which points* lie in it. A captured point can sit in the
unenumerated remainder of every level simultaneously, so the truncated martingale need not grow
along it. Nor can this be patched by a measure-theoretic argument: the conclusion is needed at
one specific point, where almost-everywhere statements say nothing.

**Bounded-error simulation is what works.** The real martingale is kept as a semantic object and
approximated by a program at a computable rate; a rational martingale is then built by walking
down the tree and splitting each node's value according to the approximations. Two properties
make this sound, and they are independent:

- *Fairness is exact by construction.* The two children are set to `x + (a−b)/2` and
  `x + (b−a)/2` for approximations `a`, `b`, so they sum to `2x` whatever the approximations
  are. Fairness never depends on approximation quality, which is why an approximate martingale
  law never has to be reasoned about.
- *A single invariant bounds the drift.* Each step moves the deviation by at most the current
  precision, so with a summable precision schedule the total drift along any path is bounded.
  Initializing the root above the true value by more than that bound then yields, in one stroke,
  both nonnegativity of the simulated capital and pointwise domination of the original.

Domination is the point: success transfers with nothing further to prove, since a capital that
dominates an unbounded one is unbounded. That is what allows a theorem whose hypothesis is a
rational-valued computable martingale to be discharged by a construction that is naturally
real-valued.

## Effective and non-effective notions are not conflated

Notions that admit a universal test and notions that do not are kept structurally distinct.
Martin-Löf randomness has a universal test because its measure bound can be enforced by
trimming; Schnorr randomness has no ordinary universal test of that enumeration-and-trimming
kind, because computability of the measure is not effectively certifiable in the same way. The
library therefore has no generic "randomness notion with a universal test" abstraction, since
it would be wrong for the second case.

Similarly, totality of a program is carried as asserted data alongside the code, never claimed
to be effectively decidable, and bundles carrying it are deliberately not enumerable.

## Verification discipline

These are enforced policies rather than periodic observations. CI builds the public spine with
warnings as errors and requires the experimental library to typecheck under the same linter
set, rejects proof placeholders in the public spine, enforces the experimental dependency
boundary, and audits the axiom policy by sweeping every declaration in the public import spine
— a sweep rather than a curated list, so a new declaration cannot introduce an axiom by being
forgotten. Key executable
definitions carry compile-time evaluation checks, so the executable layer is exercised and not
merely typechecked.
