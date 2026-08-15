/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.FiniteOpen
import AlgorithmicRandomness.Coding.FiniteOpen
import AlgorithmicRandomness.Coding.Partrec

/-!
# Prefix-free machines, and a sanitizer for arbitrary codes

A prefix-free machine is a partial computable map on bit strings whose domain is prefix-free.
Prefix-freeness is not effectively certifiable, so raw codes cannot simply be enumerated as
prefix-free machines — the same obstruction that makes the universal Martin-Löf test require
trimming rather than a plain enumeration, and the resolution is the same shape: an executable
*sanitizer* that forces every candidate to be legal while leaving compliant candidates alone.

The sanitizer accepts along an append-only chronology of halting inputs, keeping an input exactly
when it is incomparable with everything accepted so far. First arrival wins, so the result depends
on the *order of discovery* and hence on the code's syntax, not only on what it computes. Two
codes with the same denotation can sanitize to different machines when that denotation is not
prefix-free. This is not a defect and matches trimming; there is deliberately no extensionality
lemma.

## The domain convention

`machineDomain` counts *any* halt on `Encodable.encode σ` as consuming `σ`, including a halt whose
output is not the encoding of a bit string and therefore describes nothing. This is the
conservative choice: it can only make the domain larger, so the Kraft accounting later in the
development is an upper bound and stays sound. `Describes.mem_machineDomain` records that
descriptions are a special case.

The alternative — defining the domain through `Describes` — would need a canonical-output test in
the executable stages and would make the domain smaller, weakening the Kraft bounds for no gain.

## The acceptance contract

- prefix-free always: `isPrefixFreeMachine_sanitizeCode`;
- domain never grows: `machineDomain_sanitizeCode_subset`;
- domain preserved on compliant sources: `machineDomain_sanitizeCode_eq_of_prefixFree`;
- descriptions preserved on compliant sources: `describes_sanitizeCode_of_prefixFree`.

The uniform computability statement is over the product `Code × ℕ`, following trimming and
simulation: that is the form a later single universal program consumes when it dispatches on a
code drawn from its own input.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AlgorithmicRandomness

open BitString

namespace PrefixMachine

/-! ## Semantics -/

/-- `σ` is a description of `τ` under `c`. Stated against the encoding, so no decoding step and no
junk value enters the definition; injectivity of `Encodable.encode` makes `τ` determined. -/
def Describes (c : Code) (σ τ : BitString) : Prop :=
  c.eval (Encodable.encode σ) = Part.some (Encodable.encode τ)

/-- The inputs on which the machine halts. Any halt consumes the input, whether or not the output
decodes to a string. -/
def machineDomain (c : Code) : Set BitString := {σ | (c.eval (Encodable.encode σ)).Dom}

theorem Describes.mem_machineDomain {c : Code} {σ τ : BitString} (h : Describes c σ τ) :
    σ ∈ machineDomain c := by
  rw [machineDomain, Set.mem_setOf_eq, Describes] at *
  rw [h]
  trivial

theorem describes_unique {c : Code} {σ τ τ' : BitString} (h : Describes c σ τ)
    (h' : Describes c σ τ') : τ = τ' := by
  rw [Describes] at h h'
  have : Encodable.encode τ = Encodable.encode τ' := by
    have := h.symm.trans h'
    exact Part.some_injective this
  exact Encodable.encode_injective this

/-- A machine is prefix-free when its domain is. -/
def IsPrefixFreeMachine (c : Code) : Prop := PrefixFree (machineDomain c)

/-! ## Executable stages

The same shape as the discovery chronology behind trimming: each stage recomputes with more fuel,
and the trace concatenates the stages, so it is append-only and earlier decisions are never
revisited. Inputs are enumerated by `wordsOfLength`, which guarantees canonical encodings; the
extra condition `Encodable.encode σ < s` that `evaln` imposes is automatic and needs no separate
bookkeeping. -/

/-- The strings of length at most `s` on which `c` halts within fuel `s`. -/
def domainStageList (c : Code) (s : ℕ) : List BitString :=
  ((List.range (s + 1)).flatMap wordsOfLength).filterMap fun σ ↦
    if (Code.evaln s c (Encodable.encode σ)).isSome then some σ else none

/-- The append-only chronology of halting inputs. -/
def domainTrace (c : Code) : ℕ → List BitString
  | 0 => domainStageList c 0
  | s + 1 => domainTrace c s ++ domainStageList c (s + 1)

@[simp] theorem domainTrace_zero (c : Code) : domainTrace c 0 = domainStageList c 0 := rfl

@[simp] theorem domainTrace_succ (c : Code) (s : ℕ) :
    domainTrace c (s + 1) = domainTrace c s ++ domainStageList c (s + 1) := rfl

theorem domainTrace_prefix {c : Code} {s t : ℕ} (h : s ≤ t) :
    domainTrace c s <+: domainTrace c t := by
  induction t with
  | zero => rw [Nat.le_zero.mp h]
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans ⟨_, rfl⟩
    · exact List.prefix_refl _

theorem mem_range_flatMap_wordsOfLength {s : ℕ} {σ : BitString} :
    σ ∈ (List.range (s + 1)).flatMap wordsOfLength ↔ σ.length ≤ s := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨n, hn, hmem⟩
    rw [List.mem_range] at hn
    rw [length_of_mem_wordsOfLength hmem]
    omega
  · intro h
    exact ⟨σ.length, List.mem_range.mpr (by omega), mem_wordsOfLength_length σ⟩

@[simp] theorem mem_domainStageList {c : Code} {s : ℕ} {σ : BitString} :
    σ ∈ domainStageList c s ↔ σ.length ≤ s ∧ (Code.evaln s c (Encodable.encode σ)).isSome := by
  rw [domainStageList, List.mem_filterMap]
  constructor
  · rintro ⟨τ, hτ, hsome⟩
    by_cases h : (Code.evaln s c (Encodable.encode τ)).isSome
    · rw [if_pos h, Option.some_inj] at hsome
      subst hsome
      exact ⟨mem_range_flatMap_wordsOfLength.mp hτ, h⟩
    · rw [if_neg h] at hsome; exact absurd hsome (by simp)
  · rintro ⟨hlen, hsome⟩
    exact ⟨σ, mem_range_flatMap_wordsOfLength.mpr hlen, by rw [if_pos hsome]⟩

theorem mem_machineDomain_of_mem_domainStageList {c : Code} {s : ℕ} {σ : BitString}
    (h : σ ∈ domainStageList c s) : σ ∈ machineDomain c := by
  obtain ⟨-, hsome⟩ := mem_domainStageList.mp h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  exact Part.dom_iff_mem.mpr ⟨x, evaln_sound (by rw [hx]; rfl)⟩

theorem mem_machineDomain_of_mem_domainTrace {c : Code} {s : ℕ} {σ : BitString}
    (h : σ ∈ domainTrace c s) : σ ∈ machineDomain c := by
  induction s with
  | zero => exact mem_machineDomain_of_mem_domainStageList h
  | succ s ih =>
    rw [domainTrace_succ, List.mem_append] at h
    rcases h with h | h
    · exact ih h
    · exact mem_machineDomain_of_mem_domainStageList h

theorem exists_mem_domainTrace {c : Code} {σ : BitString} (h : σ ∈ machineDomain c) :
    ∃ s, σ ∈ domainTrace c s := by
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
  obtain ⟨k, hk⟩ := evaln_complete.mp hx
  refine ⟨max k σ.length, ?_⟩
  have hstage : σ ∈ domainStageList c (max k σ.length) := by
    rw [mem_domainStageList]
    refine ⟨le_max_right _ _, ?_⟩
    have := evaln_mono (le_max_left k σ.length) hk
    exact Option.isSome_iff_exists.mpr ⟨x, this⟩
  cases hmax : max k σ.length with
  | zero => rw [hmax] at hstage; exact hstage
  | succ t => rw [hmax] at hstage; exact List.mem_append.mpr (Or.inr hstage)

/-! ## The sanitizer -/

/-- `σ` is comparable with some member of `A`. -/
def comparableWith (A : List BitString) (σ : BitString) : Bool :=
  A.foldr (fun τ b ↦ b || prefixB τ σ || prefixB σ τ) false

theorem comparableWith_iff {A : List BitString} {σ : BitString} :
    comparableWith A σ = true ↔ ∃ τ ∈ A, τ <+: σ ∨ σ <+: τ := by
  rw [comparableWith]
  induction A with
  | nil => simp
  | cons ρ A ih =>
    rw [List.foldr_cons]
    simp only [Bool.or_eq_true, ih, prefixB_iff, List.mem_cons]
    constructor
    · rintro ((⟨τ, hτ, hc⟩ | h) | h)
      · exact ⟨τ, Or.inr hτ, hc⟩
      · exact ⟨ρ, Or.inl rfl, Or.inl h⟩
      · exact ⟨ρ, Or.inl rfl, Or.inr h⟩
    · rintro ⟨τ, rfl | hτ, hc | hc⟩
      · exact Or.inl (Or.inr hc)
      · exact Or.inr hc
      · exact Or.inl (Or.inl ⟨τ, hτ, Or.inl hc⟩)
      · exact Or.inl (Or.inl ⟨τ, hτ, Or.inr hc⟩)

/-- Accept `σ` exactly when it is incomparable with everything accepted so far. First arrival
wins; a repeat of an already-accepted string is rejected, which is why the preservation contract
below is about membership rather than list equality. -/
def acceptStep (A : List BitString) (σ : BitString) : List BitString :=
  if comparableWith A σ then A else A ++ [σ]

def accepted (L : List BitString) : List BitString := L.foldl acceptStep []

def sanitize (c : Code) (s : ℕ) : List BitString := accepted (domainTrace c s)

theorem prefix_acceptStep (A : List BitString) (σ : BitString) : A <+: acceptStep A σ := by
  rw [acceptStep]
  split
  · exact List.prefix_refl _
  · exact ⟨[σ], rfl⟩

theorem prefix_foldl_acceptStep (A L : List BitString) : A <+: L.foldl acceptStep A := by
  induction L generalizing A with
  | nil => exact List.prefix_refl _
  | cons σ L ih => exact (prefix_acceptStep A σ).trans (ih _)

theorem accepted_append (L M : List BitString) :
    accepted (L ++ M) = M.foldl acceptStep (accepted L) := by
  rw [accepted, accepted, List.foldl_append]

theorem prefix_accepted {L L' : List BitString} (h : L <+: L') : accepted L <+: accepted L' := by
  obtain ⟨M, rfl⟩ := h
  rw [accepted_append]
  exact prefix_foldl_acceptStep _ _

theorem mem_of_mem_foldl_acceptStep {A L : List BitString} {σ : BitString}
    (h : σ ∈ L.foldl acceptStep A) : σ ∈ A ∨ σ ∈ L := by
  induction L generalizing A with
  | nil => exact Or.inl h
  | cons τ L ih =>
    rcases ih h with h' | h'
    · rw [acceptStep] at h'
      split at h'
      · exact Or.inl h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact Or.inl h''
        · rw [List.mem_singleton] at h''
          exact Or.inr (by rw [h'']; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem τ h')

theorem mem_of_mem_accepted {L : List BitString} {σ : BitString} (h : σ ∈ accepted L) : σ ∈ L := by
  rcases mem_of_mem_foldl_acceptStep h with h' | h'
  · simp at h'
  · exact h'

/-- The accepted list is always prefix-free. -/
theorem prefixFree_foldl_acceptStep {A : List BitString}
    (hA : ∀ σ ∈ A, ∀ τ ∈ A, σ <+: τ → σ = τ) (L : List BitString) :
    ∀ σ ∈ L.foldl acceptStep A, ∀ τ ∈ L.foldl acceptStep A, σ <+: τ → σ = τ := by
  induction L generalizing A with
  | nil => exact hA
  | cons ρ L ih =>
    refine ih ?_
    rw [acceptStep]
    split
    next => exact hA
    next h =>
      intro σ hσ τ hτ hpre
      have hincomp : ∀ μ ∈ A, ¬(μ <+: ρ ∨ ρ <+: μ) := fun μ hμ hcomp ↦
        h (comparableWith_iff.mpr ⟨μ, hμ, hcomp⟩)
      rcases List.mem_append.mp hσ with hσ' | hσ' <;> rcases List.mem_append.mp hτ with hτ' | hτ'
      · exact hA σ hσ' τ hτ' hpre
      · rw [List.mem_singleton] at hτ'
        subst hτ'
        exact absurd (Or.inl hpre) (hincomp σ hσ')
      · rw [List.mem_singleton] at hσ'
        subst hσ'
        exact absurd (Or.inr hpre) (hincomp τ hτ')
      · rw [List.mem_singleton] at hσ' hτ'
        rw [hσ', hτ']

theorem prefixFree_accepted (L : List BitString) :
    PrefixFree {σ | σ ∈ accepted L} :=
  prefixFree_iff.mpr (prefixFree_foldl_acceptStep (by simp) L)

/-- With a prefix-free source, acceptance is exactly "seen before or new": comparability with the
accumulator can only mean equality, so nothing is lost. -/
private theorem mem_foldl_acceptStep_iff {L : List BitString}
    (hL : ∀ σ ∈ L, ∀ τ ∈ L, σ <+: τ → σ = τ) :
    ∀ (M A : List BitString), (∀ ρ ∈ A, ρ ∈ L) → (∀ ρ ∈ M, ρ ∈ L) →
      ∀ x, (x ∈ M.foldl acceptStep A ↔ x ∈ A ∨ x ∈ M) := by
  intro M
  induction M with
  | nil => intro A _ _ x; simp
  | cons ρ M ih =>
    intro A hA hM x
    have hkey : ∀ y, y ∈ acceptStep A ρ ↔ y ∈ A ∨ y = ρ := by
      intro y
      rw [acceptStep]
      split
      next h =>
        obtain ⟨μ, hμ, hcomp⟩ := comparableWith_iff.mp h
        have hρA : ρ ∈ A := by
          rcases hcomp with hc | hc
          · rwa [hL μ (hA μ hμ) ρ (hM ρ List.mem_cons_self) hc] at hμ
          · rwa [← hL ρ (hM ρ List.mem_cons_self) μ (hA μ hμ) hc] at hμ
        exact ⟨Or.inl, fun h' ↦ h'.elim id fun h'' ↦ h'' ▸ hρA⟩
      next => simp
    have hAsub : ∀ r ∈ acceptStep A ρ, r ∈ L := by
      intro r hr
      rcases (hkey r).mp hr with h' | rfl
      · exact hA r h'
      · exact hM r List.mem_cons_self
    rw [List.foldl_cons, ih (acceptStep A ρ) hAsub (fun r hr ↦ hM r (List.mem_cons_of_mem ρ hr)) x,
      hkey x]
    constructor
    · rintro ((h' | rfl) | h')
      · exact Or.inl h'
      · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem ρ h')
    · rintro (h' | h')
      · exact Or.inl (Or.inl h')
      · rcases List.mem_cons.mp h' with rfl | h''
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr h''

/-- A source whose halting inputs are already prefix-free loses nothing: acceptance rejects only
repeats, so the accepted *set* is the whole trace. This is a membership statement, not list
equality — the trace does repeat, and a repeat is rejected. -/
theorem mem_accepted_iff_of_prefixFree {L : List BitString}
    (hL : ∀ σ ∈ L, ∀ τ ∈ L, σ <+: τ → σ = τ) {σ : BitString} :
    σ ∈ accepted L ↔ σ ∈ L := by
  rw [accepted, mem_foldl_acceptStep_iff hL L [] (by simp) (fun _ h ↦ h) σ]
  simp

/-! ## Uniform computability

The product form over `Code × ℕ` is primary, following trimming and simulation: it is what a
single later program consumes when it dispatches on a code taken from its own input. -/

theorem primrec_comparableWith : Primrec₂ comparableWith := by
  have h : Primrec₂ fun (a : List BitString × BitString) (p : BitString × Bool) ↦
      p.2 || prefixB p.1 a.2 || prefixB a.2 p.1 :=
    (Primrec.or.comp
      (Primrec.or.comp (Primrec.snd.comp Primrec.snd)
        (primrec_prefixB.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)))
      (primrec_prefixB.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))).to₂
  exact Primrec.list_foldr Primrec.fst
    (Primrec.const (α := List BitString × BitString) false) h

theorem primrec_acceptStep : Primrec₂ acceptStep := by
  refine Primrec.ite (Primrec.eq.comp primrec_comparableWith (Primrec.const true))
    Primrec.fst ?_
  exact Primrec.list_append.comp Primrec.fst
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))

theorem primrec_accepted : Primrec accepted := by
  have h : Primrec₂ fun (_ : List BitString) (p : List BitString × BitString) ↦
      acceptStep p.1 p.2 :=
    (primrec_acceptStep.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldl Primrec.id
    (Primrec.const (α := List BitString) ([] : List BitString)) h

theorem primrec_domainStageList : Primrec fun z : Code × ℕ ↦ domainStageList z.1 z.2 := by
  unfold domainStageList
  refine Primrec.listFilterMap
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      (primrec_wordsOfLength.comp Primrec.snd)) ?_
  refine Primrec.ite (Primrec.eq.comp ?_ (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.option_isSome.comp
    (Code.primrec_evaln.comp (((Primrec.snd.comp Primrec.fst).pair
      (Primrec.fst.comp Primrec.fst)).pair (Primrec.encode.comp Primrec.snd)))

theorem primrec_domainTrace : Primrec fun z : Code × ℕ ↦ domainTrace z.1 z.2 := by
  have hstep : Primrec₂ fun (c : Code) (p : ℕ × List BitString) ↦
      p.2 ++ domainStageList c (p.1 + 1) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (primrec_domainStageList.comp
        (Primrec.fst.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))))
  refine (Primrec.nat_rec (f := fun c : Code ↦ domainStageList c 0)
    (primrec_domainStageList.comp (Primrec.id.pair (Primrec.const 0))) hstep).comp
    Primrec.fst Primrec.snd |>.of_eq fun z ↦ ?_
  obtain ⟨c, s⟩ := z
  induction s with
  | zero => rfl
  | succ s ih => rw [domainTrace_succ, ← ih]

theorem primrec_sanitize : Primrec fun z : Code × ℕ ↦ sanitize z.1 z.2 :=
  primrec_accepted.comp primrec_domainTrace

/-- The accepted list only grows with the stage. -/
theorem sanitize_prefix {c : Code} {s t : ℕ} (h : s ≤ t) : sanitize c s <+: sanitize c t :=
  prefix_accepted (domainTrace_prefix h)

/-! ## The sanitized machine as a code -/

/-- `m` is the encoding of a string accepted by stage `s`. Canonical inputs are recognized by
comparing encodings, so no decoding step appears and a non-canonical natural is never accepted —
the sanitized machine is undefined there automatically, rather than by a side condition. -/
def acceptedAt (c : Code) (s m : ℕ) : Bool :=
  (sanitize c s).foldr (fun σ b ↦ b || decide (Encodable.encode σ = m)) false

theorem acceptedAt_iff {c : Code} {s m : ℕ} :
    acceptedAt c s m = true ↔ ∃ σ ∈ sanitize c s, Encodable.encode σ = m := by
  rw [acceptedAt]
  induction sanitize c s with
  | nil => simp
  | cons ρ L ih =>
    rw [List.foldr_cons]
    simp only [Bool.or_eq_true, ih, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (⟨τ, hτ, he⟩ | he)
      · exact ⟨τ, Or.inr hτ, he⟩
      · exact ⟨ρ, Or.inl rfl, he⟩
    · rintro ⟨τ, rfl | hτ, he⟩
      · exact Or.inr he
      · exact Or.inl ⟨τ, hτ, he⟩

theorem acceptedAt_encode_iff {c : Code} {s : ℕ} {σ : BitString} :
    acceptedAt c s (Encodable.encode σ) = true ↔ σ ∈ sanitize c s := by
  rw [acceptedAt_iff]
  exact ⟨fun ⟨τ, hτ, he⟩ ↦ Encodable.encode_injective he ▸ hτ, fun h ↦ ⟨σ, h, rfl⟩⟩

theorem primrec_acceptedAt : Primrec fun z : (Code × ℕ) × ℕ ↦ acceptedAt z.1.1 z.1.2 z.2 := by
  have h : Primrec₂ fun (z : (Code × ℕ) × ℕ) (p : BitString × Bool) ↦
      p.2 || decide (Encodable.encode p.1 = z.2) :=
    (Primrec.or.comp (Primrec.snd.comp Primrec.snd)
      (primrecPred_iff_primrec_decide.mp
        (Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst)))).to₂
  exact Primrec.list_foldr (primrec_sanitize.comp Primrec.fst)
    (Primrec.const (α := (Code × ℕ) × ℕ) false) h

-- `acceptedAt` unfolds through `sanitize`, `domainTrace` and `evaln`; leaving it reducible makes
-- the composition below blow up in `whnf`, exactly as the coded arithmetic did in `Simulate`.
attribute [local irreducible] acceptedAt

/-- Run `c` on `m`, but only once `m` has been accepted. -/
def sanitizedEval (c : Code) (m : ℕ) : Part ℕ :=
  (Nat.rfind fun s ↦ Part.some (acceptedAt c s m)).bind fun _ ↦ c.eval m

theorem partrec_sanitizedEval : Partrec fun z : Code × ℕ ↦ sanitizedEval z.1 z.2 := by
  unfold sanitizedEval
  refine Partrec.bind (Partrec.rfind ?_) ?_
  · have h : Computable fun w : (Code × ℕ) × ℕ ↦ acceptedAt w.1.1 w.2 w.1.2 :=
      (primrec_acceptedAt.comp
        (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
          (Primrec.snd.comp Primrec.fst))).to_comp
    exact Computable₂.partrec₂ h.to₂
  · exact Partrec₂.comp Code.eval_part (Primrec.fst.comp Primrec.fst).to_comp
      (Primrec.snd.comp Primrec.fst).to_comp |>.to₂

theorem partrec_sanitizedEval_fixed (c : Code) : Nat.Partrec (sanitizedEval c) :=
  Partrec.nat_iff.mp (partrec_sanitizedEval.comp
    (Computable.pair (Computable.const c) Computable.id))

/-! ## The sanitized code, and the acceptance contract -/

/-- The sanitized machine, as an actual code. -/
noncomputable def sanitizeCode (c : Code) : Code :=
  (Code.exists_code.mp (partrec_sanitizedEval_fixed c)).choose

theorem eval_sanitizeCode (c : Code) : (sanitizeCode c).eval = sanitizedEval c :=
  (Code.exists_code.mp (partrec_sanitizedEval_fixed c)).choose_spec

/-- Once an input is accepted the machine simply runs the source, so the two evaluations agree
wherever the sanitized one is defined. -/
theorem sanitizedEval_eq_of_mem_sanitize {c : Code} {σ : BitString} {s : ℕ}
    (hs : σ ∈ sanitize c s) :
    sanitizedEval c (Encodable.encode σ) = c.eval (Encodable.encode σ) := by
  refine Part.ext fun x ↦ ?_
  rw [sanitizedEval, Part.mem_bind_iff]
  refine ⟨fun hb ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨_, -, hx⟩ := hb
    exact hx
  obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun t ↦ acceptedAt c t (Encodable.encode σ))
    (acceptedAt_encode_iff.mpr hs)
  exact ⟨n, hn, hx⟩

theorem mem_machineDomain_sanitizeCode_iff {c : Code} {σ : BitString} :
    σ ∈ machineDomain (sanitizeCode c) ↔ ∃ s, σ ∈ sanitize c s := by
  rw [machineDomain, Set.mem_setOf_eq, eval_sanitizeCode]
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    rw [sanitizedEval, Part.mem_bind_iff] at hx
    obtain ⟨s, hs, -⟩ := hx
    exact ⟨s, acceptedAt_encode_iff.mp (by simpa using Nat.rfind_spec hs)⟩
  · rintro ⟨s, hs⟩
    rw [sanitizedEval_eq_of_mem_sanitize hs]
    exact mem_machineDomain_of_mem_domainTrace (mem_of_mem_accepted hs)

/-- **Prefix-free always.** Each stage is prefix-free and the stages are nested, so any two
accepted strings already coexist at a common stage. -/
theorem isPrefixFreeMachine_sanitizeCode (c : Code) : IsPrefixFreeMachine (sanitizeCode c) := by
  rw [IsPrefixFreeMachine, prefixFree_iff]
  intro σ hσ τ hτ hpre
  obtain ⟨s, hs⟩ := mem_machineDomain_sanitizeCode_iff.mp hσ
  obtain ⟨t, ht⟩ := mem_machineDomain_sanitizeCode_iff.mp hτ
  exact prefixFree_iff.mp (prefixFree_accepted (domainTrace c (max s t))) σ
    ((sanitize_prefix (le_max_left s t)).subset hs) τ
    ((sanitize_prefix (le_max_right s t)).subset ht) hpre

/-- **The domain never grows.** -/
theorem machineDomain_sanitizeCode_subset (c : Code) :
    machineDomain (sanitizeCode c) ⊆ machineDomain c := by
  intro σ hσ
  obtain ⟨s, hs⟩ := mem_machineDomain_sanitizeCode_iff.mp hσ
  exact mem_machineDomain_of_mem_domainTrace (mem_of_mem_accepted hs)

private theorem prefixFree_domainTrace {c : Code} (h : IsPrefixFreeMachine c) (s : ℕ) :
    ∀ α ∈ domainTrace c s, ∀ β ∈ domainTrace c s, α <+: β → α = β := fun α hα β hβ hpre ↦
  prefixFree_iff.mp h α (mem_machineDomain_of_mem_domainTrace hα) β
    (mem_machineDomain_of_mem_domainTrace hβ) hpre

/-- **The domain is preserved on compliant sources.** -/
theorem machineDomain_sanitizeCode_eq_of_prefixFree {c : Code} (h : IsPrefixFreeMachine c) :
    machineDomain (sanitizeCode c) = machineDomain c := by
  refine Set.Subset.antisymm (machineDomain_sanitizeCode_subset c) fun σ hσ ↦ ?_
  obtain ⟨s, hs⟩ := exists_mem_domainTrace hσ
  exact mem_machineDomain_sanitizeCode_iff.mpr
    ⟨s, (mem_accepted_iff_of_prefixFree (prefixFree_domainTrace h s)).mpr hs⟩

/-- Sanitizing never invents a description: this direction needs no hypothesis. -/
theorem describes_of_describes_sanitizeCode {c : Code} {σ τ : BitString}
    (h : Describes (sanitizeCode c) σ τ) : Describes c σ τ := by
  obtain ⟨s, hs⟩ := mem_machineDomain_sanitizeCode_iff.mp h.mem_machineDomain
  rw [Describes, eval_sanitizeCode, sanitizedEval_eq_of_mem_sanitize hs] at h
  exact h

/-- **Descriptions are preserved on compliant sources.** -/
theorem describes_sanitizeCode_of_prefixFree {c : Code} (h : IsPrefixFreeMachine c)
    (σ τ : BitString) : Describes (sanitizeCode c) σ τ ↔ Describes c σ τ := by
  refine ⟨describes_of_describes_sanitizeCode, fun hd ↦ ?_⟩
  obtain ⟨s, hs⟩ := exists_mem_domainTrace hd.mem_machineDomain
  have hacc : σ ∈ sanitize c s :=
    (mem_accepted_iff_of_prefixFree (prefixFree_domainTrace h s)).mpr hs
  rw [Describes, eval_sanitizeCode, sanitizedEval_eq_of_mem_sanitize hacc]
  exact hd

end PrefixMachine

end AlgorithmicRandomness
