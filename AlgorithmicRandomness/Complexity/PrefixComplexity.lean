/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Complexity.Universal

/-!
# Prefix-free Kolmogorov complexity

`prefixComplexity τ` is the length of a shortest description of `τ` under the optimal universal
prefix-free machine. It is defined as an infimum and is noncomputable; the executable object is
`prefixComplexityStage`, a primitive recursive finite approximation. This is the same split as
`gridCDF` against `dyadicCDF`: the semantic definition says what the quantity *is*, and a separate
coded object is what a program can run.

Three bridges connect the layers, and each is used in both directions downstream:

```text
        short semantic description
                  ↕            prefixComplexity_le_iff_exists_description
          prefixComplexity τ ≤ k
                  ↕            prefixComplexity_le_iff_exists_stage
    some finite stage discovers a bound ≤ k
```

The definition is well posed because every string has *some* description: a machine whose domain
is the single empty string and which outputs `τ` there is prefix-free, and optimality converts its
description into a universal one. That machine exists only for this argument and is private.

The optimality consequence is stated at the level of descriptions
(`prefixComplexity_le_add_of_describes`) rather than as an invariance theorem. Invariance relates
two complexity functions and would need a second optimal machine together with a proof that it is
description-complete; the description-level bound is stronger for every current consumer, since it
assumes nothing about the competing machine beyond prefix-freeness.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AlgorithmicRandomness

open BitString

/-! ## Every string has a description -/

private def literalOut (τ : BitString) (m : ℕ) : Option ℕ :=
  if m = Encodable.encode ([] : BitString) then some (Encodable.encode τ) else none

private theorem partrec_literalOut (τ : BitString) :
    Nat.Partrec fun m ↦ (literalOut τ m : Part ℕ) := by
  refine Partrec.nat_iff.mp (Computable.ofOption ?_)
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const _))
    (Primrec.option_some.comp (Primrec.const _)) (Primrec.const none) |>.to_comp

private noncomputable def literalCode (τ : BitString) : Code :=
  (Code.exists_code.mp (partrec_literalOut τ)).choose

private theorem eval_literalCode (τ : BitString) (m : ℕ) :
    (literalCode τ).eval m = (literalOut τ m : Part ℕ) :=
  congrFun (Code.exists_code.mp (partrec_literalOut τ)).choose_spec m

private theorem literalOut_isSome_iff (τ σ : BitString) :
    (literalOut τ (Encodable.encode σ)).isSome ↔ σ = [] := by
  rw [literalOut]
  by_cases h : σ = []
  · subst h; rw [if_pos rfl]; simp
  · rw [if_neg (fun he ↦ h (Encodable.encode_injective he))]; simp [h]

private theorem machineDomain_literalCode (τ : BitString) :
    PrefixMachine.machineDomain (literalCode τ) = {([] : BitString)} := by
  ext σ
  rw [PrefixMachine.machineDomain, Set.mem_setOf_eq, eval_literalCode, Set.mem_singleton_iff,
    Part.ofOption_dom, literalOut_isSome_iff]

private noncomputable def literalMachine (τ : BitString) : PrefixFreeMachine where
  program := literalCode τ
  prefixFree := by
    rw [PrefixMachine.IsPrefixFreeMachine, machineDomain_literalCode]
    exact Set.pairwise_singleton _ _

private theorem describes_literalMachine (τ : BitString) :
    PrefixMachine.Describes (literalMachine τ).program [] τ := by
  rw [PrefixMachine.Describes, show (literalMachine τ).program = literalCode τ from rfl,
    eval_literalCode, literalOut, if_pos rfl]
  rfl

/-- **Totality of the definition**: every string has a universal description. -/
theorem exists_describes_universal (τ : BitString) :
    ∃ p, PrefixMachine.Describes universalPrefixCode p τ := by
  obtain ⟨d, hd⟩ := isOptimal_universalMachine (literalMachine τ)
  obtain ⟨q, hq, -⟩ := hd (describes_literalMachine τ)
  exact ⟨q, hq⟩

/-! ## Prefix complexity -/

/-- The length of a shortest universal description. Noncomputable by construction; the executable
content is `prefixComplexityStage`. -/
noncomputable def prefixComplexity (τ : BitString) : ℕ :=
  sInf {k | ∃ p : BitString, p.length = k ∧ PrefixMachine.Describes universalPrefixCode p τ}

theorem exists_describes_length_prefixComplexity (τ : BitString) :
    ∃ p, p.length = prefixComplexity τ ∧ PrefixMachine.Describes universalPrefixCode p τ := by
  obtain ⟨p, hp⟩ := exists_describes_universal τ
  have hne : Set.Nonempty
      {k | ∃ q : BitString, q.length = k ∧ PrefixMachine.Describes universalPrefixCode q τ} :=
    ⟨p.length, p, rfl, hp⟩
  exact Nat.sInf_mem hne

theorem prefixComplexity_le_length {p τ : BitString}
    (h : PrefixMachine.Describes universalPrefixCode p τ) : prefixComplexity τ ≤ p.length :=
  Nat.sInf_le ⟨p, rfl, h⟩

/-- **The semantic bridge.** A complexity bound and a short description are the same information.
-/
theorem prefixComplexity_le_iff_exists_description {τ : BitString} {k : ℕ} :
    prefixComplexity τ ≤ k ↔
      ∃ p, PrefixMachine.Describes universalPrefixCode p τ ∧ p.length ≤ k := by
  constructor
  · intro h
    obtain ⟨p, hlen, hp⟩ := exists_describes_length_prefixComplexity τ
    exact ⟨p, hp, by omega⟩
  · rintro ⟨p, hp, hlen⟩
    exact (prefixComplexity_le_length hp).trans hlen

/-- **Optimality, at the level of descriptions.** -/
theorem prefixComplexity_le_add_of_describes (M : PrefixFreeMachine) :
    ∃ d, ∀ {p τ : BitString}, PrefixMachine.Describes M.program p τ →
      prefixComplexity τ ≤ p.length + d := by
  obtain ⟨d, hd⟩ := isOptimal_universalMachine M
  refine ⟨d, fun {p τ} hp ↦ ?_⟩
  obtain ⟨q, hq, hlen⟩ := hd hp
  exact (prefixComplexity_le_length hq).trans hlen

/-! ## Finite stages

A `List ℕ` minimum carried as `Option ℕ`, with `none` meaning "no description found yet". A fold
rather than `List.min?`, because the pinned mathlib has no `Primrec` lemma for the latter — the
same accommodation as elsewhere in the coded layer. `getD` makes the step total without a sentinel:
at `none` the fold takes the new value, and `min k k = k`. -/

private def minOpt (L : List ℕ) : Option ℕ :=
  L.foldr (fun k acc ↦ some (min k (acc.getD k))) none

private theorem minOpt_nil : minOpt [] = none := rfl

private theorem mem_of_minOpt_eq_some :
    ∀ {L : List ℕ} {k : ℕ}, minOpt L = some k → k ∈ L := by
  intro L
  induction L with
  | nil => intro k h; rw [minOpt_nil] at h; exact absurd h (by simp)
  | cons a L ih =>
    intro k h
    have hstep : minOpt (a :: L) = some (min a ((minOpt L).getD a)) := rfl
    rw [hstep, Option.some_inj] at h
    subst h
    cases hL : minOpt L with
    | none => simp
    | some l =>
      rw [Option.getD_some]
      rcases min_cases a l with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he]; exact List.mem_cons_self
      · rw [he]; exact List.mem_cons_of_mem a (ih hL)

private theorem exists_minOpt_le {L : List ℕ} {k : ℕ} (h : k ∈ L) :
    ∃ l, minOpt L = some l ∧ l ≤ k := by
  induction L with
  | nil => exact absurd h (by simp)
  | cons a L ih =>
    have hstep : minOpt (a :: L) = some (min a ((minOpt L).getD a)) := rfl
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨_, hstep, min_le_left _ _⟩
    · obtain ⟨l, hl, hlk⟩ := ih h'
      refine ⟨_, hstep, ?_⟩
      rw [hl, Option.getD_some]
      exact le_trans (min_le_right a l) hlk

/-- The candidate description lengths visible at stage `s`. The length bound only makes the list
finite: `evaln` already refuses inputs whose encoding exceeds the fuel. -/
private noncomputable def stageLengths (s : ℕ) (τ : BitString) : List ℕ :=
  ((List.range (s + 1)).flatMap wordsOfLength).filterMap fun p ↦
    if PrefixMachine.DescribesAt universalPrefixCode s p τ then some p.length else none

private theorem mem_stageLengths {s : ℕ} {τ : BitString} {k : ℕ} :
    k ∈ stageLengths s τ ↔
      ∃ p : BitString, p.length ≤ s ∧ PrefixMachine.DescribesAt universalPrefixCode s p τ = true
        ∧ p.length = k := by
  rw [stageLengths, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hsome⟩
    by_cases h : PrefixMachine.DescribesAt universalPrefixCode s p τ = true
    · rw [if_pos h, Option.some_inj] at hsome
      exact ⟨p, PrefixMachine.mem_range_flatMap_wordsOfLength.mp hp, h, hsome⟩
    · rw [if_neg h] at hsome; exact absurd hsome (by simp)
  · rintro ⟨p, hlen, hd, rfl⟩
    exact ⟨p, PrefixMachine.mem_range_flatMap_wordsOfLength.mpr hlen, by rw [if_pos hd]⟩

/-- The stage approximation: the least description length found by stage `s`, or `none`. -/
noncomputable def prefixComplexityStage (s : ℕ) (τ : BitString) : Option ℕ :=
  minOpt (stageLengths s τ)

theorem prefixComplexityStage_sound {s : ℕ} {τ : BitString} {k : ℕ}
    (h : prefixComplexityStage s τ = some k) : prefixComplexity τ ≤ k := by
  obtain ⟨p, -, hd, rfl⟩ := mem_stageLengths.mp (mem_of_minOpt_eq_some h)
  exact prefixComplexity_le_length (PrefixMachine.describes_of_describesAt hd)

theorem prefixComplexityStage_mono {s t : ℕ} {τ : BitString} {k : ℕ} (hst : s ≤ t)
    (h : prefixComplexityStage s τ = some k) :
    ∃ l ≤ k, prefixComplexityStage t τ = some l := by
  obtain ⟨p, hlen, hd, rfl⟩ := mem_stageLengths.mp (mem_of_minOpt_eq_some h)
  obtain ⟨l, hl, hlk⟩ := exists_minOpt_le
    (mem_stageLengths.mpr ⟨p, hlen.trans hst, PrefixMachine.describesAt_mono hst hd, rfl⟩)
  exact ⟨l, hlk, hl⟩

/-- The boolean-facing corollary: once a description has been found it stays found. -/
theorem prefixComplexityStage_isSome_mono {s t : ℕ} {τ : BitString} (hst : s ≤ t)
    (h : (prefixComplexityStage s τ).isSome) : (prefixComplexityStage t τ).isSome := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨l, -, hl⟩ := prefixComplexityStage_mono hst hk
  rw [hl]
  rfl

theorem prefixComplexityStage_complete (τ : BitString) :
    ∃ s, prefixComplexityStage s τ = some (prefixComplexity τ) := by
  obtain ⟨p, hlen, hp⟩ := exists_describes_length_prefixComplexity τ
  obtain ⟨s₀, hs₀⟩ := PrefixMachine.exists_describesAt hp
  refine ⟨max s₀ p.length, ?_⟩
  obtain ⟨l, hl, hlp⟩ := exists_minOpt_le (mem_stageLengths.mpr
    ⟨p, le_max_right _ _, PrefixMachine.describesAt_mono (le_max_left _ _) hs₀, rfl⟩)
  have hstage : prefixComplexityStage (max s₀ p.length) τ = some l := hl
  have hle := prefixComplexityStage_sound hstage
  rw [hstage, Option.some_inj]
  omega

/-- **The executable bridge.** A complexity bound is exactly what some finite stage certifies. -/
theorem prefixComplexity_le_iff_exists_stage {τ : BitString} {k : ℕ} :
    prefixComplexity τ ≤ k ↔ ∃ s l, prefixComplexityStage s τ = some l ∧ l ≤ k := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := prefixComplexityStage_complete τ
    exact ⟨s, prefixComplexity τ, hs, h⟩
  · rintro ⟨s, l, hs, hlk⟩
    exact (prefixComplexityStage_sound hs).trans hlk

/-- The stage function is a coded finite approximation, not merely a semantic one. -/
theorem primrec_prefixComplexityStage :
    Primrec fun z : ℕ × BitString ↦ prefixComplexityStage z.1 z.2 := by
  have hcand : Primrec fun z : ℕ × BitString ↦ stageLengths z.1 z.2 := by
    unfold stageLengths
    refine Primrec.listFilterMap
      (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
        (primrec_wordsOfLength.comp Primrec.snd)) ?_
    refine Primrec.ite (Primrec.eq.comp ?_ (Primrec.const true))
      (Primrec.option_some.comp (Primrec.list_length.comp Primrec.snd)) (Primrec.const none)
    exact PrefixMachine.primrec_describesAt.comp
      (Primrec.pair (Primrec.pair (Primrec.const universalPrefixCode)
        (Primrec.fst.comp Primrec.fst))
        (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))
  have hstep : Primrec₂ fun (_ : ℕ × BitString) (q : ℕ × Option ℕ) ↦
      (some (min q.1 (q.2.getD q.1)) : Option ℕ) :=
    (Primrec.option_some.comp
      (Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.option_getD.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp Primrec.snd)))).to₂
  exact Primrec.list_foldr hcand (Primrec.const none) hstep

end AlgorithmicRandomness
