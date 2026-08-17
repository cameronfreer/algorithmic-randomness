# Prefix-free machines

A prefix-free machine in this library is not a new interpreter. It is a mathlib partial-recursive
program code bundled with a proof that its halting inputs form a prefix-free set. Everything else —
the sanitizer, the universal machine, the Kraft–Chaitin allocator — is a different way of
constructing that same bundled object.

## The representation

```lean
structure PrefixFreeMachine where
  program : Nat.Partrec.Code
  prefixFree : PrefixMachine.IsPrefixFreeMachine program
```

[`Complexity/PrefixMachine.lean:585`](../AlgorithmicRandomness/Complexity/PrefixMachine.lean)

`Nat.Partrec.Code` is mathlib's syntax for partial recursive functions `ℕ →. ℕ`. Bit strings travel
through it by encoding:

```lean
def Describes (c : Code) (σ τ : BitString) : Prop :=
  c.eval (Encodable.encode σ) = Part.some (Encodable.encode τ)
```

```text
bit string σ  --encode-->  ℕ  --c.eval-->  Part ℕ  --must equal-->  encode τ
```

`Part ℕ` is partial computation: divergence is the empty `Part`, termination with `m` is
`Part.some m`. Stating `Describes` against the encoding rather than through `decode` means no
partiality and no junk value enters the definition, and injectivity of `encode` makes the described
string unique.

## What prefix-free means

```lean
def machineDomain (c : Code) : Set BitString := {σ | (c.eval (Encodable.encode σ)).Dom}

def IsPrefixFreeMachine (c : Code) : Prop := PrefixFree (machineDomain c)
```

`PrefixFree` says distinct members are incompatible: neither is a prefix of the other.

The domain convention is deliberately conservative. *Any* halt on `encode σ` consumes `σ`, including
a halt whose output is not the canonical encoding of any bit string and therefore describes nothing.
Such a halt still counts against the Kraft bound. This can only make the domain larger, so the
counting arguments downstream remain upper bounds and stay sound. Defining the domain through
`Describes` instead would need a canonical-output test in the executable stages and would weaken
those bounds for no gain.

## Why prefix-freeness is a proof field

Whether an arbitrary partial recursive program has prefix-free domain is not effectively decidable,
so the library does not pretend to certify it computationally. Instead `program` is executable data,
`prefixFree` is asserted evidence, and arbitrary codes are made legal by a sanitizer.

This is the same discipline as `NatFunctionCode`, where a program travels with a proof that it
computes the stated *total* function: the property that cannot be tested is carried as data, and
bundles carrying it are deliberately not enumerable.

## The sanitizer

For a raw `Code`, the halting bit-string inputs are enumerated in stages —

```lean
def domainStageList (c : Code) (s : ℕ) : List BitString
def domainTrace (c : Code) : ℕ → List BitString
```

— and a string is accepted only when it is incomparable with everything accepted so far:

```lean
def acceptStep (A : List BitString) (σ : BitString) : List BitString :=
  if comparableWith A σ then A else A ++ [σ]
```

First arrival wins. The sanitized function waits until its input has been accepted, then runs the
original program unchanged:

```lean
def sanitizedEval (c : Code) (m : ℕ) : Part ℕ :=
  (Nat.rfind fun s ↦ Part.some (acceptedAt c s m)).bind fun _ ↦ c.eval m
```

This is proved partial recursive, so mathlib supplies an actual program code:

```lean
noncomputable def sanitizeCode (c : Code) : Code :=
  (Code.exists_code.mp (partrec_sanitizedEval_fixed c)).choose
```

The contract is: the domain is always prefix-free; it never grows; and when the source domain was
already prefix-free, both the domain and every description are unchanged. `PrefixFreeMachine.ofCode`
packages the result.

Two things are worth being precise about. Preservation is a *membership* statement, not list
equality — the trace repeats entries as fuel grows, and a repeat of an already-accepted string is
rejected, so the accepted list differs from the trace even for a compliant source while the accepted
set does not. And the sanitizer is **not extensional**: the chronology depends on `evaln`, hence on
the code's syntax, so two codes with the same denotation can sanitize differently when that
denotation is not prefix-free. There is deliberately no extensionality lemma.

*Noncomputable* here means Lean is choosing syntax whose denotation is the proved partial-recursive
function. The result is still a term of the concrete `Code` datatype — not a quotient, not a
semantic machine — but the chosen syntax does not kernel-reduce under `#eval`.

## The optimal universal machine

Inputs are self-delimiting:

```lean
def tag (e : ℕ) (σ : BitString) : BitString := List.replicate e true ++ false :: σ
```

```text
1 1 1 … 1 0 payload
└─── e ──┘  └─ p ─┘
```

The `false` terminates the unary index, so distinct indices are incompatible at the delimiter:

```lean
theorem compatible_tag_iff :
    BitString.Compatible (tag e σ) (tag j τ) ↔ e = j ∧ BitString.Compatible σ τ
```

The evaluator parses the tag, decodes the `e`-th code, and runs it on the payload *through the
sanitizer*, so no hypothesis about that code is needed:

```lean
def universalEval (m : ℕ) : Part ℕ :=
  (Part.ofOption ((canonicalBitString m).bind parseTag)).bind fun q ↦
    PrefixMachine.sanitizedEval (Denumerable.ofNat Code q.1) (Encodable.encode q.2)
```

[`Complexity/Universal.lean:140`](../AlgorithmicRandomness/Complexity/Universal.lean)

`Code.exists_code` again yields one concrete `universalPrefixCode`. Its domain is prefix-free for a
structural reason — different tags are incompatible, and within one tag the sanitized candidate's
domain is prefix-free — so the proof is two cases and no measure theory. It is optimal because a
prefix-free machine with index `e` is simulated on `tag e p`, at an overhead of exactly `e + 1`
bits.

The universal program calls `sanitizedEval` *dynamically*, on a code decoded from its own input;
that is what the uniform computability statement over `Code × ℕ` supplies. The transformation
`sanitizeCode` is noncomputable and appears only on the proof side, to state the operational
theorem. The program never computes it.

## Kraft–Chaitin machines

The second construction builds a machine from requests:

```lean
structure KraftRequest where
  length : ℕ
  output : BitString
```

The allocator maintains free slots and assignments —

```lean
structure AllocationState where
  assigned : List Assignment
  free : List BitString
```

— and gives every request a codeword of exactly the requested length while keeping everything
prefix-free. A `KraftRequestTrace` supplies an append-only computable request stream whose total
weight never exceeds one.

The resulting machine searches for the stage at which its input was assigned and emits the stored
output. It is again proved partial recursive and extracted as one `Nat.Partrec.Code`. Its central
theorem is

```lean
theorem describes_machineCode_iff (p τ : BitString) :
    PrefixMachine.Describes R.machineCode p τ ↔
      ∃ s, ∃ a ∈ R.assignmentsStage s, a.codeword = p ∧ a.output = τ
```

[`Complexity/KraftChaitin.lean:1008`](../AlgorithmicRandomness/Complexity/KraftChaitin.lean)

and the machine domain, its prefix-freeness, and the theorem that every request is fulfilled are all
derived from it.

Two points carry the allocator. Fulfilment takes the **longest** adequate slot — the free list is
kept in strictly decreasing length order, so it is the first slot short enough. Taking the shortest
instead breaks the invariant: from the empty string, a length-3 request leaves free lengths `3, 2,
1`, and serving a following length-2 request from the length-1 slot would create a second length-2
slot and leave nothing for a later length-1 request. That pattern is an executable `#guard` in the
file. And availability is a counting argument: distinct lengths all exceeding `n` have total weight
strictly below `2⁻ⁿ`, so a request still inside the budget must find a slot.

## Summary

```text
Nat.Partrec.Code
  + interpretation on encoded bit strings
  + proof that the interpreted domain is prefix-free
  = PrefixFreeMachine
```

Three constructions produce that bundle: the **sanitizer**, from an arbitrary code; the **tagged
universal interpreter**, which is optimal; and the **Kraft–Chaitin allocator**, from a request
stream inside the Kraft budget.

See [architecture.md](architecture.md) for the design decisions these rest on, in particular why
codes and denotations stay separate and where uniformity is load-bearing.
