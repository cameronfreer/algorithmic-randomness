/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.Basic
import Mathlib.Computability.PartrecCode

/-!
# Coding spike: staged enumeration of bit strings from partial recursive codes

This file validates `Nat.Partrec.Code` as the enumeration model for effective open sets,
below the effective-topology API. A code `c` names, for each family index `n`, a c.e. set of
bit strings: run `c` on paired inputs `Nat.pair n k` and decode successful outputs. The
stage `stringStage c n s` runs inputs `k ≤ s` with fuel `s`; stages are cumulative
(`stringStage_mono`) and enumerate exactly the semantic outputs
(`exists_mem_stringStage_iff`).

`Code.evaln`'s first argument is *fuel* — it bounds recursion depth and admits only inputs
below itself — not a literal step count. We use only its exported interface: `evaln_mono`,
`evaln_sound`, `evaln_complete` (plus `Code.primrec_evaln` for later uniformity arguments).

The concrete acceptance program `replicateTrueFamilyCode` enumerates, at family index `n`,
exactly the string `true^n`, with executable stage checks and a semantic denotation theorem.

## Fallback criterion

`Nat.Partrec.Code` is rejected (in favor of a bespoke machine) only if either:

* **R1 (executability)**: stages of the concrete program cannot be executed — `#eval` fails
  to run `stringStage` and kernel reduction (`#guard`/`decide`) is also unavailable; or
* **R2 (abstraction)**: proving the denotation theorem or the stage theorems requires case
  analysis on `evaln`'s internal definition, beyond the exported interface above.

Neither fired in this file. Whether `curry`/`smn` compose well enough for the uniform
trimming construction is judged at the universal-test milestone, not here.
-/

open Nat.Partrec (Code)

namespace AlgorithmicRandomness

/-! ## Staged enumeration -/

/-- Run `c` on input `k` with fuel `s`, decoding success as a bit string. Divergence within
the fuel bound and outputs that are not valid `List Bool` codes both give `none`. -/
def stringOut (c : Code) (s k : ℕ) : Option BitString :=
  (Code.evaln s c k).bind Encodable.decode

theorem stringOut_mono {c : Code} {s t k : ℕ} (h : s ≤ t) {σ : BitString}
    (hs : stringOut c s k = some σ) : stringOut c t k = some σ := by
  rw [stringOut, Option.bind_eq_some_iff] at hs
  obtain ⟨m, hm, hdec⟩ := hs
  rw [stringOut, Code.evaln_mono h hm]
  exact hdec

/-- Stage `s` of the `n`-th set enumerated by `c`: the strings produced from paired inputs
`Nat.pair n k` for `k ≤ s`, with fuel `s`. -/
def stringStage (c : Code) (n s : ℕ) : Finset BitString :=
  ((List.range (s + 1)).filterMap fun k ↦ stringOut c s (Nat.pair n k)).toFinset

@[simp]
theorem mem_stringStage {c : Code} {n s : ℕ} {σ : BitString} :
    σ ∈ stringStage c n s ↔ ∃ k ≤ s, stringOut c s (Nat.pair n k) = some σ := by
  simp [stringStage, List.mem_filterMap, Nat.lt_succ_iff]

/-- Stages are cumulative. -/
theorem stringStage_mono {c : Code} {n : ℕ} {s t : ℕ} (h : s ≤ t) :
    stringStage c n s ⊆ stringStage c n t := by
  intro σ hσ
  rw [mem_stringStage] at hσ ⊢
  obtain ⟨k, hk, hout⟩ := hσ
  exact ⟨k, hk.trans h, stringOut_mono h hout⟩

/-- `c` enumerates `σ` into its `n`-th set: some paired input halts (unboundedly) on an
output decoding to `σ`. Noncanonical output codes are accepted. -/
def EnumeratesString (c : Code) (n : ℕ) (σ : BitString) : Prop :=
  ∃ k m, m ∈ c.eval (Nat.pair n k) ∧ Encodable.decode m = some σ

theorem stringStage_sound {c : Code} {n s : ℕ} {σ : BitString} (h : σ ∈ stringStage c n s) :
    EnumeratesString c n σ := by
  rw [mem_stringStage] at h
  obtain ⟨k, -, hout⟩ := h
  rw [stringOut, Option.bind_eq_some_iff] at hout
  obtain ⟨m, hm, hdec⟩ := hout
  exact ⟨k, m, Code.evaln_sound hm, hdec⟩

theorem stringStage_complete {c : Code} {n : ℕ} {σ : BitString}
    (h : EnumeratesString c n σ) : ∃ s, σ ∈ stringStage c n s := by
  obtain ⟨k, m, hm, hdec⟩ := h
  obtain ⟨s₀, hs₀⟩ := Code.evaln_complete.mp hm
  refine ⟨max s₀ k, mem_stringStage.mpr ⟨k, le_max_right s₀ k, ?_⟩⟩
  rw [stringOut, Code.evaln_mono (le_max_left s₀ k) hs₀]
  exact hdec

/-- The stages of the `n`-th set enumerate exactly its semantic members. -/
theorem exists_mem_stringStage_iff {c : Code} {n : ℕ} {σ : BitString} :
    (∃ s, σ ∈ stringStage c n s) ↔ EnumeratesString c n σ :=
  ⟨fun ⟨_, hs⟩ ↦ stringStage_sound hs, stringStage_complete⟩

/-! ## The concrete acceptance program -/

/-- `pure` on `ℕ →. ℕ` is pointwise `Part.some`; `Code.eval` produces this shape. -/
private theorem pfun_pure_apply (m n : ℕ) : (pure m : ℕ →. ℕ) n = Part.some m := rfl

/-- Pointwise unfolding of `Code.eval` on a composition, definitionally. -/
private theorem eval_comp_apply (cf cg : Code) (n : ℕ) :
    (cf.comp cg).eval n = (cg.eval n).bind cf.eval := rfl

/-- The recursion step of `replicateTrueCode`: on `Nat.pair a (Nat.pair y i)`, output
`Nat.pair 1 i + 1`, which is `encode (true :: decode i)`. -/
private def stepCode : Code :=
  Code.comp Code.succ (Code.pair (Code.const 1) (Code.comp Code.right Code.right))

/-- On input `n`, output the canonical code of the string `true^n`. Built from raw
combinators: primitive recursion with base `Code.zero` (`0 = encode []`) and step
`succ ∘ pair (const 1) (right ∘ right)`, fed `Nat.pair 0 n`. -/
def replicateTrueCode : Code :=
  Code.comp (Code.prec Code.zero stepCode) (Code.pair Code.zero Code.id)

private theorem encode_replicate_succ (n : ℕ) :
    Encodable.encode (List.replicate (n + 1) true) =
      Nat.pair 1 (Encodable.encode (List.replicate n true)) + 1 := by
  rw [List.replicate_succ, Encodable.encode_list_cons]
  rfl

private theorem eval_prec_replicate (n : ℕ) :
    (Code.prec Code.zero stepCode).eval (Nat.pair 0 n) =
      Part.some (Encodable.encode (List.replicate n true)) := by
  induction n with
  | zero => rw [Code.eval_prec_zero]; rfl
  | succ n ih =>
    rw [Code.eval_prec_succ, ih, encode_replicate_succ]
    simp [stepCode, eval_comp_apply, Code.eval, Seq.seq, Code.eval_const, Nat.unpair_pair]

/-- Denotation of the worker: `replicateTrueCode` computes `n ↦ encode (true^n)`. -/
theorem eval_replicateTrueCode (n : ℕ) :
    replicateTrueCode.eval n = Part.some (Encodable.encode (List.replicate n true)) := by
  have hin : (Code.pair Code.zero Code.id).eval n = Part.some (Nat.pair 0 n) := by
    simp [Code.eval, Seq.seq, Code.eval_id, pfun_pure_apply]
  rw [replicateTrueCode, eval_comp_apply, hin, Part.bind_some, eval_prec_replicate]

/-- The uniform family: on paired input `Nat.pair n k`, ignore `k` and output the canonical
code of `true^n`. This is the prefix family of the all-`true`s computable point. -/
def replicateTrueFamilyCode : Code :=
  Code.comp replicateTrueCode Code.left

theorem eval_replicateTrueFamilyCode (n k : ℕ) :
    replicateTrueFamilyCode.eval (Nat.pair n k) =
      Part.some (Encodable.encode (List.replicate n true)) := by
  rw [replicateTrueFamilyCode, eval_comp_apply]
  simp [Code.eval, Nat.unpair_pair, eval_replicateTrueCode]

/-- The acceptance theorem: the `n`-th set enumerated by `replicateTrueFamilyCode` is
exactly `{true^n}`. -/
theorem enumeratesString_replicateTrueFamilyCode {n : ℕ} {σ : BitString} :
    EnumeratesString replicateTrueFamilyCode n σ ↔ σ = List.replicate n true := by
  constructor
  · rintro ⟨k, m, hm, hdec⟩
    rw [eval_replicateTrueFamilyCode, Part.mem_some_iff] at hm
    subst hm
    rw [Encodable.encodek] at hdec
    exact (Option.some_injective _ hdec).symm
  · rintro rfl
    exact ⟨0, Encodable.encode (List.replicate n true),
      by rw [eval_replicateTrueFamilyCode]; exact Part.mem_some _, Encodable.encodek _⟩

section Examples
-- executable acceptance checks; fuel constants found experimentally with `#eval`
set_option linter.hashCommand false

-- fuel demands grow with `evaln`'s input guard: stage `s` admits only intermediate values
-- `< s`, and the paired inputs inside `prec` reach `Nat.pair 0 (Nat.pair 1 3) = 100` at `n = 2`
#guard ([] : BitString) ∈ stringStage replicateTrueFamilyCode 0 1
#guard [true] ∈ stringStage replicateTrueFamilyCode 1 3
#guard [true, true] ∈ stringStage replicateTrueFamilyCode 2 101
#guard [false] ∉ stringStage replicateTrueFamilyCode 1 32
#guard stringStage replicateTrueFamilyCode 2 3 ⊆ stringStage replicateTrueFamilyCode 2 101

end Examples

end AlgorithmicRandomness
