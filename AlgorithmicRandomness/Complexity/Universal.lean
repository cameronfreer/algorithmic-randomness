/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Complexity.PrefixMachine

/-!
# An optimal universal prefix-free machine

One code, `universalPrefixCode`, that simulates every prefix-free machine with only additive
overhead. The construction is the tagged sanitized interpreter: an input is read as a unary index
`e`, a delimiter, and a payload `p`, and the machine runs the `e`-th code on `p` — through the
sanitizer, so that no assumption about the `e`-th code is needed.

Two things make this work, and both were built for it.

The universal program calls `PrefixMachine.sanitizedEval` *dynamically*, on a code decoded from its
own input. That is what the product-uniform statement over `Code × ℕ` supplies. The transformation
`PrefixMachine.sanitizeCode` is noncomputable and appears only on the proof side, to state the
operational theorem; the program never computes it.

Unary tags are *self-delimiting*, so the domain is prefix-free for a structural reason rather than
an analytic one: `compatible_tag_iff` says two tagged strings are comparable only when their
indices agree, at which point comparability reduces to the sanitized candidate's own domain. The
proof is two cases and no measure theory.

## Architecture

Following the universal Martin-Löf test, the universal machine is *one actual code*. Its domain
admits a description as a union over machine indices, but that description is
`machineDomain_universalPrefixCode`, a theorem about the extracted code's behaviour, and never its
definition.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AlgorithmicRandomness

open BitString

/-! ## Self-delimiting tags -/

/-- The index `e` in unary, a `false` delimiter, then the payload. -/
def tag (e : ℕ) (σ : BitString) : BitString := List.replicate e true ++ false :: σ

@[simp] theorem tag_zero (σ : BitString) : tag 0 σ = false :: σ := rfl

theorem tag_succ (e : ℕ) (σ : BitString) : tag (e + 1) σ = true :: tag e σ := by
  rw [tag, tag, List.replicate_succ, List.cons_append]

@[simp] theorem length_tag (e : ℕ) (σ : BitString) : (tag e σ).length = σ.length + e + 1 := by
  rw [tag, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Read the unary index, the delimiter, and the payload. -/
def parseTag (ρ : BitString) : Option (ℕ × BitString) :=
  match ρ.dropWhile id with
  | [] => none
  | _ :: rest => some ((ρ.takeWhile id).length, rest)

@[simp] theorem parseTag_nil : parseTag [] = none := rfl

@[simp] theorem parseTag_cons_false (ρ : BitString) : parseTag (false :: ρ) = some (0, ρ) := rfl

theorem parseTag_cons_true (ρ : BitString) :
    parseTag (true :: ρ) = (parseTag ρ).map fun q ↦ (q.1 + 1, q.2) := by
  rw [parseTag, parseTag, List.dropWhile_cons_of_pos (by rfl), List.takeWhile_cons_of_pos (by rfl)]
  cases h : ρ.dropWhile id with
  | nil => simp
  | cons b rest => simp

@[simp] theorem parseTag_tag (e : ℕ) (σ : BitString) : parseTag (tag e σ) = some (e, σ) := by
  induction e with
  | zero => simp
  | succ e ih => rw [tag_succ, parseTag_cons_true, ih, Option.map_some]

/-- **Every input the machine proceeds on really is a tag.** The converse of `parseTag_tag`, and
what makes both the domain description and prefix-freeness available. -/
theorem eq_tag_of_parseTag_eq_some {ρ : BitString} {e : ℕ} {σ : BitString}
    (h : parseTag ρ = some (e, σ)) : ρ = tag e σ := by
  induction ρ generalizing e with
  | nil => simp at h
  | cons b ρ ih =>
    cases b with
    | false =>
      rw [parseTag_cons_false, Option.some_inj, Prod.mk.injEq] at h
      rw [← h.1, ← h.2, tag_zero]
    | true =>
      rw [parseTag_cons_true, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, hqe⟩ := h
      rw [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ : e = q.1 + 1 ∧ σ = q.2 := ⟨hqe.1.symm, hqe.2.symm⟩
      rw [tag_succ, ← ih (by rw [hq])]

theorem primrec_parseTag : Primrec parseTag := by
  have hstep : Primrec₂ fun (ρ : BitString) (p : Bool × List Bool) ↦
      (some ((ρ.takeWhile id).length, p.2) : Option (ℕ × BitString)) :=
    (Primrec.option_some.comp
      (Primrec.pair
        ((Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)).comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))).to₂
  refine (Primrec.list_casesOn (Primrec.list_dropWhile Primrec.id)
    (Primrec.const none) hstep).of_eq fun ρ ↦ ?_
  rw [parseTag]
  cases ρ.dropWhile id <;> rfl

/-! ## Tags are self-delimiting -/

theorem prefix_tag_iff {e j : ℕ} {σ τ : BitString} :
    tag e σ <+: tag j τ ↔ e = j ∧ σ <+: τ := by
  induction e generalizing j with
  | zero =>
    cases j with
    | zero => simp [List.cons_prefix_cons]
    | succ j => simp [tag_succ, List.cons_prefix_cons]
  | succ e ih =>
    cases j with
    | zero => simp [tag_succ, List.cons_prefix_cons]
    | succ j => rw [tag_succ, tag_succ, List.cons_prefix_cons, ih]; simp

/-- **Self-delimitation.** Two tagged strings are comparable only when their indices agree, and
then only as their payloads are. This is the whole reason the universal domain is prefix-free. -/
theorem compatible_tag_iff {e j : ℕ} {σ τ : BitString} :
    BitString.Compatible (tag e σ) (tag j τ) ↔ e = j ∧ BitString.Compatible σ τ := by
  rw [BitString.Compatible, BitString.Compatible, prefix_tag_iff, prefix_tag_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, Or.inl h⟩
    · exact ⟨rfl, Or.inr h⟩
  · rintro ⟨rfl, h | h⟩
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, h⟩

/-! ## The universal machine -/

/-- Read a tag, then run the indexed code on the payload — through the sanitizer, so no hypothesis
about that code is needed. The output is forwarded unchanged. -/
def universalEval (m : ℕ) : Part ℕ :=
  (Part.ofOption ((canonicalBitString m).bind parseTag)).bind fun q ↦
    PrefixMachine.sanitizedEval (Denumerable.ofNat Code q.1) (Encodable.encode q.2)

-- `sanitizedEval` unfolds through the whole sanitizer; leaving it reducible makes the composition
-- below time out in `whnf`, as it did inside `PrefixMachine` itself.
attribute [local irreducible] PrefixMachine.sanitizedEval

theorem partrec_universalEval : Nat.Partrec universalEval := by
  have harg : Computable fun w : ℕ × (ℕ × BitString) ↦
      (Denumerable.ofNat Code w.2.1, Encodable.encode w.2.2) :=
    Computable.pair ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.snd)).to_comp
      (Primrec.encode.comp (Primrec.snd.comp Primrec.snd)).to_comp
  refine Partrec.nat_iff.mp (Partrec.bind (Computable.ofOption ?_) ?_)
  · exact (Primrec.option_bind primrec_canonicalBitString
      (primrec_parseTag.comp Primrec.snd).to₂).to_comp
  · exact PrefixMachine.partrec_sanitizedEval.comp harg

/-- **The universal prefix-free machine**, as one actual code. -/
noncomputable def universalPrefixCode : Code :=
  (Code.exists_code.mp partrec_universalEval).choose

theorem eval_universalPrefixCode : universalPrefixCode.eval = universalEval :=
  (Code.exists_code.mp partrec_universalEval).choose_spec

/-- **The operational theorem.** On a tagged input the universal machine is exactly the sanitized
indexed machine. -/
theorem describes_universal_tag_iff {e : ℕ} {p τ : BitString} :
    PrefixMachine.Describes universalPrefixCode (tag e p) τ ↔
      PrefixMachine.Describes (PrefixMachine.sanitizeCode (Denumerable.ofNat Code e)) p τ := by
  rw [PrefixMachine.Describes, PrefixMachine.Describes, eval_universalPrefixCode,
    PrefixMachine.eval_sanitizeCode, universalEval, canonicalBitString_encode, Option.bind_some,
    parseTag_tag, Part.coe_some, Part.bind_some]

/-- **The domain description**, as a theorem about the extracted code rather than its definition.
-/
theorem mem_machineDomain_universalPrefixCode_iff {σ : BitString} :
    σ ∈ PrefixMachine.machineDomain universalPrefixCode ↔
      ∃ e p, σ = tag e p ∧
        p ∈ PrefixMachine.machineDomain
          (PrefixMachine.sanitizeCode (Denumerable.ofNat Code e)) := by
  rw [PrefixMachine.machineDomain, Set.mem_setOf_eq, eval_universalPrefixCode, universalEval,
    canonicalBitString_encode, Option.bind_some]
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    rw [Part.mem_bind_iff] at hx
    obtain ⟨q, hq, hx'⟩ := hx
    rw [Part.mem_ofOption] at hq
    refine ⟨q.1, q.2, eq_tag_of_parseTag_eq_some (by rw [hq]), ?_⟩
    rw [PrefixMachine.machineDomain, Set.mem_setOf_eq, PrefixMachine.eval_sanitizeCode]
    exact Part.dom_iff_mem.mpr ⟨x, hx'⟩
  · rintro ⟨e, p, rfl, hp⟩
    rw [PrefixMachine.machineDomain, Set.mem_setOf_eq, PrefixMachine.eval_sanitizeCode] at hp
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hp
    refine Part.dom_iff_mem.mpr ⟨x, Part.mem_bind_iff.mpr ⟨(e, p), ?_, hx⟩⟩
    rw [Part.mem_ofOption, parseTag_tag]
    rfl

theorem machineDomain_universalPrefixCode :
    PrefixMachine.machineDomain universalPrefixCode
      = ⋃ e : ℕ, tag e ''
          PrefixMachine.machineDomain (PrefixMachine.sanitizeCode (Denumerable.ofNat Code e)) := by
  ext σ
  rw [mem_machineDomain_universalPrefixCode_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨e, p, rfl, hp⟩
    exact ⟨e, p, hp, rfl⟩
  · rintro ⟨e, p, hp, rfl⟩
    exact ⟨e, p, rfl, hp⟩

/-- **The universal machine is prefix-free.** Unequal indices are incompatible at the delimiter;
equal indices reduce to the sanitized candidate, which is prefix-free by construction. -/
theorem isPrefixFreeMachine_universalPrefixCode :
    PrefixMachine.IsPrefixFreeMachine universalPrefixCode := by
  rw [PrefixMachine.IsPrefixFreeMachine, prefixFree_iff]
  intro σ hσ τ hτ hpre
  obtain ⟨e, p, rfl, hp⟩ := mem_machineDomain_universalPrefixCode_iff.mp hσ
  obtain ⟨j, q, rfl, hq⟩ := mem_machineDomain_universalPrefixCode_iff.mp hτ
  obtain ⟨rfl, hcomp⟩ := compatible_tag_iff.mp (Or.inl hpre)
  have hpf := PrefixMachine.isPrefixFreeMachine_sanitizeCode (Denumerable.ofNat Code e)
  rcases hcomp with h | h
  · rw [prefixFree_iff.mp hpf p hp q hq h]
  · rw [prefixFree_iff.mp hpf q hq p hp h]

noncomputable def universalMachine : PrefixFreeMachine :=
  ⟨universalPrefixCode, isPrefixFreeMachine_universalPrefixCode⟩

/-! ## Optimality -/

/-- `U` simulates `M` with additive overhead `d`. -/
def PrefixFreeMachine.SimulatesWithOverhead (U M : PrefixFreeMachine) (d : ℕ) : Prop :=
  ∀ {p τ : BitString}, PrefixMachine.Describes M.program p τ →
    ∃ q, PrefixMachine.Describes U.program q τ ∧ q.length ≤ p.length + d

/-- `U` is optimal when it simulates every prefix-free machine with some additive overhead. -/
def PrefixFreeMachine.IsOptimal (U : PrefixFreeMachine) : Prop :=
  ∀ M : PrefixFreeMachine, ∃ d, U.SimulatesWithOverhead M d

/-- **Optimality.** The overhead is the machine's own index plus one — the length of its tag. This
is where the sanitizer's preservation contract is consumed: `M` is prefix-free by assumption, so
sanitizing its code leaves every description intact. -/
theorem isOptimal_universalMachine : universalMachine.IsOptimal := by
  intro M
  refine ⟨Encodable.encode M.program + 1, ?_⟩
  intro p τ hd
  refine ⟨tag (Encodable.encode M.program) p, ?_, ?_⟩
  · rw [show universalMachine.program = universalPrefixCode from rfl, describes_universal_tag_iff,
      Denumerable.ofNat_encode]
    exact (PrefixMachine.describes_sanitizeCode_of_prefixFree M.prefixFree p τ).mpr hd
  · rw [length_tag]
    omega

end AlgorithmicRandomness
