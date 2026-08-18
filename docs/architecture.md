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

## Normalization before construction

A martingale that succeeds may still lose everything it gains infinitely often. Constructions
downstream of success need more than success, and the library supplies it by *normalizing* first
rather than by strengthening every later argument.

The savings normalization splits capital into a banked part and an active part, keeps the active
part bounded, and banks a fixed *fraction* of any gain rather than a fixed amount. The fraction
matters: banking half is free of truncated subtraction on `ℚ≥0`, and it makes the counting
identity relating capital to the number of deposits cancel exactly. Success then forces
unboundedly many deposits, and each deposit contributes a definite amount, so the banked part is
itself unbounded — a stronger conclusion than the original success, obtained without any
positivity assumption on the active part.

What this buys is a martingale whose capital can be confined to a bounded interval while still
oscillating within it. That is the object the differentiability argument needs, and it cannot be
built from success alone. It also explains a constraint that looks arbitrary from outside: the
oscillation targets must be *interior* to the confining bounds. A fair martingale confined to an
interval that attains an endpoint is frozen at that endpoint forever, so a construction
oscillating between the endpoints of its own bounds is impossible. The oscillator therefore
crosses two interior levels while remaining inside strictly wider hard bounds, and the bound
proof appeals to the savings property rather than to nonnegativity.

## The cumulative function is built at dyadic points, not from a measure

A tree martingale determines a measure, and that measure has a cumulative distribution function.
The library does not construct it that way. The cumulative function is defined directly at the
endpoints of dyadic intervals, by a fold along the string.

The reason is the form of the theorem it has to feed. The chord slope across a cylinder must
equal the capital there *exactly*, with no error term and no almost-everywhere qualification,
because the eventual argument evaluates it at one specific point. Routing through a measure would
make the slope a statement about the measure of an interval, recovering the capital only up to
identifications that are invisible pointwise. Defined directly, the identity is definitional
arithmetic.

Three further choices follow from the same discipline:

- **Cut points, not cells.** A level is indexed by the `2ⁿ + 1` points `k / 2ⁿ` rather than by its
  `2ⁿ` cells. This treats `0` and `1` uniformly, and — more importantly — pins each dyadic point
  to an integer index, so that *global well-definedness* becomes a comparison of natural numbers
  after refining two levels to a common one. The alternative is a normal-form argument about
  binary strings modulo trailing zeros, which is exactly what the integer indexing avoids.
- **Half-open cells and closed intervals are different objects.** Cells partition; chords are
  taken across closed intervals. Conflating them fails at points whose binary expansion is
  eventually constant, which sit at an endpoint of every sufficiently long prefix interval. Both
  are provided, and the closed version is why no "not a dyadic rational" hypothesis appears
  anywhere in the differentiability argument.
- **The unit interval is the domain; the ambient function is derived.** A computable Lipschitz
  function is presented as a function on `[0, 1]` together with a program giving its exact values
  at the dyadic cut points, and the function on `ℝ` is obtained from it canonically by constant
  extension. A structure with a bare `ℝ → ℝ` field would overclaim: a function agreeing with
  computable data on `[0, 1]` need not be computable anywhere outside it.

Extension off the dyadic points is McShane's theorem, not a density-and-limits argument — a
real-valued function Lipschitz on a subset extends to the whole space with no completeness or
density input. Density enters only to show the extension is *unique* on `[0, 1]`, which is what
licenses treating it as the cumulative function rather than as one of many.

## Termination bookkeeping appears only where it is earned

Several coded constructions carry explicit fuel: a step budget, a proof that some budget
suffices, and primitive recursive arithmetic in the budget. This is unavoidable where a program
runs *another* program, since the outer program's totality then depends on the inner one's.

It is not unavoidable elsewhere, and the library does not pay for it elsewhere. Where a
construction consumes a bundle that already carries totality as data, the evaluator is total and
computable, and the construction can be arranged to recurse on a numeric parameter rather than to
fold over a structure. The grid program is the case in point: it recurses on the cut index, so
composition suffices and nothing about termination needs to be said. The distinction to keep in
view is whether the code being run arrived as raw syntax or as part of a bundle whose totality was
established when the bundle was built.

Relatedly, uniformity is not free and is not always needed. It is load-bearing wherever a program
receives another program as input and dispatches on it — trimming, the universal test, threshold
enumeration. A construction that consumes a bundle and emits one total evaluation code needs no
uniform syntactic transformer, and stating one would be a stronger claim than the development
supports.

## Effective and non-effective notions are not conflated

Notions that admit a universal test and notions that do not are kept structurally distinct.
Martin-Löf randomness has a universal test because its measure bound can be enforced by
trimming; Schnorr randomness has no ordinary universal test of that enumeration-and-trimming
kind, because computability of the measure is not effectively certifiable in the same way. The
library therefore has no generic "randomness notion with a universal test" abstraction, since
it would be wrong for the second case.

Similarly, totality of a program is carried as asserted data alongside the code, never claimed
to be effectively decidable, and bundles carrying it are deliberately not enumerable.

## Complexity is relative to one machine, and accounting is separated from execution

Prefix complexity is defined against a *single* optimal universal prefix-free machine, constructed
as one actual program code. It is not defined as an infimum over a class of machines, and no
"machine" abstraction is introduced. Optimality is then a theorem about that code, and it is what
lets any other prefix-free machine's descriptions bound the fixed complexity function — which is
the only reason a machine built to satisfy a request stream says anything about complexity at all.

The construction that produces such request streams forced a second separation. Requests are
generated *chronologically*, because enumeration is append-only and monotonicity of the trace has
to be definitional; but their total weight is bounded *by level*, because that is where the
geometric series lives. Reconciling the two orders after the fact would be a permutation argument
over a list with genuine repetitions. Instead each request carries a private origin tag, erased at
the public boundary: chronology stays definitional, and the weight proof regroups by tag with the
list structure intact. Deduplicating the trace at any point would be wrong, since the same request
can legitimately arise at different stages.

See [prefix-free-machines.md](prefix-free-machines.md) for the representation and the three
constructions built on it.

## Verification discipline

These are enforced policies rather than periodic observations. CI builds the public spine with
warnings as errors and requires the experimental library to typecheck under the same linter
set, rejects proof placeholders in the public spine, enforces the experimental dependency
boundary, and audits the axiom policy by sweeping every declaration in the public import spine
— a sweep rather than a curated list, so a new declaration cannot introduce an axiom by being
forgotten. Key executable
definitions carry compile-time evaluation checks, so the executable layer is exercised and not
merely typechecked.
