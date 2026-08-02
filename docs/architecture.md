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

Any function whose computability must be proved runs on `Nat` and `List`. `Finset`, `ℚ≥0`,
`ℝ≥0`, and measures appear only in correctness statements.

This is forced by the ambient library rather than chosen: mathlib supplies no
`Primcodable (Finset α)` and no `Primcodable ℚ≥0`, so an algorithm written over those types
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

## Effective and non-effective notions are not conflated

Notions that admit a universal test and notions that do not are kept structurally distinct.
Martin-Löf randomness has a universal test because its measure bound can be enforced by
trimming; Schnorr randomness does not, because computability of the measure is not effectively
certifiable in the same way. The library therefore has no generic "randomness notion with a
universal test" abstraction, since it would be wrong for the second case.

Similarly, totality of a program is carried as asserted data alongside the code, never claimed
to be effectively decidable, and bundles carrying it are deliberately not enumerable.

## Verification discipline

Every module in the stable spine is free of `sorry`, and CI enforces both that and the
boundary against the experimental library. Headline results are checked to depend only on the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Executable definitions carry
compile-time evaluation checks, so the executable layer is exercised and not merely typechecked.
