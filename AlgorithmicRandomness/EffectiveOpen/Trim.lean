/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.FiniteOpen
import AlgorithmicRandomness.EffectiveOpen.Code
import Mathlib.Computability.Primrec.List

/-!
# Executable trimming of coded c.e. open sets

Trimming forces a coded uniformly c.e. family to obey a dyadic measure budget while removing
as little as possible: enumerate the source family in a fixed chronological order and greedily
accept each newly discovered cylinder whenever accepting it keeps the exact weight within
budget.

## Representation

The executable layer runs entirely on `List BitString` and `ℕ`, never on `Finset` or `ℚ≥0`.
This is forced: mathlib provides no `Primcodable (Finset α)` and no `Primcodable ℚ≥0`, so a
`Finset`/`ℚ≥0` algorithm could not be proved `Partrec` and hence could not be turned into a
`Code`. `Finset`, `finiteOpenWeight`, and `ℚ≥0` appear only in correctness statements, never
inside a function whose computability is required. Filtering steps are written as folds rather
than with `List.filter`/bounded quantifiers because mathlib's `Primrec` versions of those are
not parameterized in a second argument.

## Chronology

`trace` is append-only by construction: stage `s + 1`'s list is stage `s`'s list plus a
suffix. Greedy decisions are therefore never revisited. A string may be re-emitted at a later
stage; this is harmless, because acceptance is idempotent and rejection is monotone
(`finiteOpenWeight_mono`), so no novelty test is needed.
-/

open Nat.Partrec (Code)
open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## The append-only discovery trace -/

/-- The append-only chronology of discoveries: ordered by stage, then by input. -/
def trace (c : Code) (n s : ℕ) : List BitString :=
  Nat.rec (stringStageList c n 0) (fun s' IH ↦ IH ++ stringStageList c n (s' + 1)) s

@[simp] theorem trace_zero (c : Code) (n : ℕ) : trace c n 0 = stringStageList c n 0 := rfl

@[simp] theorem trace_succ (c : Code) (n s : ℕ) :
    trace c n (s + 1) = trace c n s ++ stringStageList c n (s + 1) := rfl

theorem trace_prefix_succ (c : Code) (n s : ℕ) : trace c n s <+: trace c n (s + 1) :=
  ⟨stringStageList c n (s + 1), rfl⟩

/-- Stages of the trace grow by appending, so earlier decisions can never be revisited. -/
theorem trace_prefix {c : Code} {n s t : ℕ} (h : s ≤ t) : trace c n s <+: trace c n t := by
  induction t with
  | zero => rw [Nat.le_zero.mp h]
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (trace_prefix_succ c n t)
    · rw [Nat.le_antisymm h hge]

theorem trace_toFinset (c : Code) (n s : ℕ) : (trace c n s).toFinset = stringStage c n s := by
  induction s with
  | zero => rw [trace_zero, stringStageList_toFinset]
  | succ s ih =>
    rw [trace_succ, List.toFinset_append, ih, stringStageList_toFinset]
    exact Finset.union_eq_right.mpr (stringStage_mono (Nat.le_succ s))

@[simp]
theorem mem_trace {c : Code} {n s : ℕ} {σ : BitString} :
    σ ∈ trace c n s ↔ σ ∈ stringStage c n s := by
  rw [← List.mem_toFinset, trace_toFinset]

/-! ## The greedy fold -/

/-- Accept `σ` when doing so keeps the exact weight within the dyadic budget `2⁻ᵇ`. -/
def acceptStep (b : ℕ) (A : List BitString) (σ : BitString) : List BitString :=
  if weightLe b (A ++ [σ]) then A ++ [σ] else A

/-- Greedily fold the acceptance test along the chronology. -/
def accepted (b : ℕ) (L : List BitString) : List BitString := L.foldl (acceptStep b) []

theorem weightLe_nil (b : ℕ) : weightLe b [] = true := by
  rw [weightLe_iff]
  simp [finiteOpenWeight, totalWeight, minimize]

theorem prefix_acceptStep (b : ℕ) (A : List BitString) (σ : BitString) :
    A <+: acceptStep b A σ := by
  unfold acceptStep
  split
  · exact ⟨[σ], rfl⟩
  · exact List.prefix_refl A

theorem prefix_foldl_acceptStep (b : ℕ) (A L : List BitString) :
    A <+: L.foldl (acceptStep b) A := by
  induction L generalizing A with
  | nil => exact List.prefix_refl A
  | cons σ L ih => exact (prefix_acceptStep b A σ).trans (ih _)

theorem accepted_append (b : ℕ) (L M : List BitString) :
    accepted b (L ++ M) = M.foldl (acceptStep b) (accepted b L) := by
  rw [accepted, accepted, List.foldl_append]

/-- Trimming decisions are never revisited: a longer chronology extends the accepted list. -/
theorem prefix_accepted {b : ℕ} {L L' : List BitString} (h : L <+: L') :
    accepted b L <+: accepted b L' := by
  obtain ⟨M, rfl⟩ := h
  rw [accepted_append]
  exact prefix_foldl_acceptStep b _ M

theorem mem_foldl_acceptStep {b : ℕ} {A L : List BitString} {σ : BitString}
    (h : σ ∈ L.foldl (acceptStep b) A) : σ ∈ A ∨ σ ∈ L := by
  induction L generalizing A with
  | nil => exact Or.inl h
  | cons τ L ih =>
    rcases ih h with h' | h'
    · unfold acceptStep at h'
      split at h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h'')))
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem τ h')

/-- Trimming only ever accepts strings that were actually enumerated. -/
theorem mem_of_mem_accepted {b : ℕ} {L : List BitString} {σ : BitString}
    (h : σ ∈ accepted b L) : σ ∈ L := by
  rcases mem_foldl_acceptStep h with h' | h'
  · exact absurd h' (List.not_mem_nil)
  · exact h'

theorem weightLe_foldl_acceptStep {b : ℕ} {A : List BitString} (hA : weightLe b A = true)
    (L : List BitString) : weightLe b (L.foldl (acceptStep b) A) = true := by
  induction L generalizing A with
  | nil => exact hA
  | cons σ L ih =>
    refine ih ?_
    unfold acceptStep
    split
    · assumption
    · exact hA

/-- The fold invariant: every trimmed list obeys its budget. -/
theorem weightLe_accepted (b : ℕ) (L : List BitString) : weightLe b (accepted b L) = true :=
  weightLe_foldl_acceptStep (weightLe_nil b) L

theorem finiteOpenWeight_accepted_le (b : ℕ) (L : List BitString) :
    finiteOpenWeight (accepted b L).toFinset ≤ (2⁻¹ : ℚ≥0) ^ b :=
  (weightLe_iff b _).mp (weightLe_accepted b L)

theorem foldl_acceptStep_eq_append {b : ℕ} {L : List BitString}
    (hL : finiteOpenWeight L.toFinset ≤ (2⁻¹ : ℚ≥0) ^ b) :
    ∀ (A M : List BitString), (∀ τ ∈ A, τ ∈ L) → (∀ τ ∈ M, τ ∈ L) →
      M.foldl (acceptStep b) A = A ++ M := by
  intro A M
  induction M generalizing A with
  | nil => intro _ _; simp
  | cons σ M ih =>
    intro hA hM
    have hσ : σ ∈ L := hM σ List.mem_cons_self
    have hstep : acceptStep b A σ = A ++ [σ] := by
      rw [acceptStep, if_pos]
      refine (weightLe_iff b _).mpr (le_trans (finiteOpenWeight_mono ?_) hL)
      intro τ hτ
      rw [List.mem_toFinset, List.mem_append] at hτ
      rw [List.mem_toFinset]
      rcases hτ with hτ | hτ
      · exact hA τ hτ
      · rw [List.mem_singleton.mp hτ]; exact hσ
    rw [List.foldl_cons, hstep, ih _ (fun τ hτ ↦ ?_) fun τ hτ ↦ hM τ (List.mem_cons_of_mem σ hτ)]
    · simp
    · rcases List.mem_append.mp hτ with h | h
      · exact hA τ h
      · rw [List.mem_singleton.mp h]; exact hσ

/-- If the source already obeys the budget, trimming changes nothing. -/
theorem accepted_eq_self {b : ℕ} {L : List BitString}
    (hL : finiteOpenWeight L.toFinset ≤ (2⁻¹ : ℚ≥0) ^ b) : accepted b L = L := by
  rw [accepted, foldl_acceptStep_eq_append hL [] L (by simp) fun _ h ↦ h, List.nil_append]

/-! ## Trimmed stages -/

/-- Level `n` of the trim of `c` at offset `d`: trim `c`'s level `n + d` to budget `2⁻⁽ⁿ⁺ᵈ⁾`. -/
def trimAccepted (c : Code) (d n s : ℕ) : List BitString :=
  accepted (n + d) (trace c (n + d) s)

theorem prefix_trimAccepted {c : Code} {d n s t : ℕ} (h : s ≤ t) :
    trimAccepted c d n s <+: trimAccepted c d n t :=
  prefix_accepted (trace_prefix h)

theorem mem_stringStage_of_mem_trimAccepted {c : Code} {d n s : ℕ} {σ : BitString}
    (h : σ ∈ trimAccepted c d n s) : σ ∈ stringStage c (n + d) s :=
  mem_trace.mp (mem_of_mem_accepted h)

theorem finiteOpenWeight_trimAccepted_le (c : Code) (d n s : ℕ) :
    finiteOpenWeight (trimAccepted c d n s).toFinset ≤ (2⁻¹ : ℚ≥0) ^ (n + d) :=
  finiteOpenWeight_accepted_le _ _

theorem trimAccepted_eq_trace {c : Code} {d n s : ℕ}
    (h : finiteOpenWeight (stringStage c (n + d) s) ≤ (2⁻¹ : ℚ≥0) ^ (n + d)) :
    trimAccepted c d n s = trace c (n + d) s :=
  accepted_eq_self (by rwa [trace_toFinset])

/-! ## Computability

Everything above is primitive recursive, uniformly in the source code, the offset, the level,
and the stage. This is what lets the whole construction be turned into a single `Code`, and
the *uniform* statements below (not merely their pointwise instances) are what a dynamically
extracted candidate code requires.
-/

theorem primrec_trace : Primrec fun z : (Code × ℕ) × ℕ ↦ trace z.1.1 z.1.2 z.2 := by
  unfold trace
  refine (Primrec.nat_rec (α := Code × ℕ)
    (f := fun z : Code × ℕ ↦ stringStageList z.1 z.2 0)
    (g := fun (z : Code × ℕ) (p : ℕ × List BitString) ↦ p.2 ++ stringStageList z.1 z.2 (p.1 + 1))
    ?_ ?_).comp Primrec.fst Primrec.snd
  · exact primrec_stringStageList.comp (Primrec.id.pair (Primrec.const 0))
  · exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (primrec_stringStageList.comp
        (Primrec.fst.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))))

theorem primrec_accepted : Primrec₂ accepted :=
  Primrec.list_foldl (β := BitString) (σ := List BitString)
    (f := fun z : ℕ × List BitString ↦ z.2) (g := fun _ ↦ [])
    (h := fun z p ↦ if weightLe z.1 (p.1 ++ [p.2]) = true then p.1 ++ [p.2] else p.1)
    Primrec.snd (Primrec.const [])
    (Primrec.ite
      (Primrec.eq.comp
        (primrec_weightLe.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))))
        (Primrec.const true))
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))
      (Primrec.fst.comp Primrec.snd))

theorem primrec_trimAccepted :
    Primrec fun z : ((Code × ℕ) × ℕ) × ℕ ↦ trimAccepted z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  unfold trimAccepted
  have hlevel : Primrec fun z : ((Code × ℕ) × ℕ) × ℕ ↦ z.1.2 + z.1.1.2 :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact primrec_accepted.comp hlevel
    (primrec_trace.comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair hlevel).pair
      Primrec.snd))

/-! ## The trimmed code -/

/-- On paired input `⟨n, j⟩`, search for a stage at which the `n`-th trimmed list has more than
`j` entries, and return the `j`-th one. -/
def trimEnum (c : Code) (d : ℕ) : ℕ →. ℕ := fun input ↦
  (Nat.rfind fun s ↦
      Part.some (decide (input.unpair.2 < (trimAccepted c d input.unpair.1 s).length))).map
    fun s ↦ Encodable.encode ((trimAccepted c d input.unpair.1 s).getD input.unpair.2 [])

/-- The uniform enumeration function, in the source code, the offset, and the input together.
This uniform statement — not merely its pointwise instances — is what a dynamically extracted
candidate code requires downstream. -/
def trimEnumUniform : (Code × ℕ) × ℕ →. ℕ := fun z ↦ trimEnum z.1.1 z.1.2 z.2

theorem partrec_trimEnumUniform : Partrec trimEnumUniform := by
  have hacc : Primrec fun q : ((Code × ℕ) × ℕ) × ℕ ↦
      trimAccepted q.1.1.1 q.1.1.2 q.1.2.unpair.1 q.2 :=
    primrec_trimAccepted.comp
      ((((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd)
  refine Partrec.map (Partrec.rfind ?_) ?_
  · exact Computable₂.partrec₂ (primrec_decide (Primrec.nat_lt.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.list_length.comp hacc))).to_comp.to₂
  · exact (Primrec.encode.comp ((Primrec.list_getD []).comp hacc
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))).to_comp.to₂

theorem partrec_trimEnum' (c : Code) (d : ℕ) : Partrec (trimEnum c d) :=
  (partrec_trimEnumUniform.comp
    (Computable.pair (Computable.const (c, d)) Computable.id)).of_eq fun _ ↦ rfl

theorem partrec_trimEnum (c : Code) (d : ℕ) : Nat.Partrec (trimEnum c d) :=
  Partrec.nat_iff.mp (partrec_trimEnum' c d)

/-- The trimming code: a genuine `Code`, obtained from the uniform computability theorem. -/
noncomputable def trimCode (c : Code) (d : ℕ) : Code :=
  (Code.exists_code.mp (partrec_trimEnum c d)).choose

theorem eval_trimCode (c : Code) (d : ℕ) : (trimCode c d).eval = trimEnum c d :=
  (Code.exists_code.mp (partrec_trimEnum c d)).choose_spec

/-- Semantics of the trimmed code: it enumerates exactly the greedily accepted strings. -/
theorem enumeratesString_trimCode {c : Code} {d n : ℕ} {σ : BitString} :
    EnumeratesString (trimCode c d) n σ ↔ ∃ s, σ ∈ trimAccepted c d n s := by
  constructor
  · rintro ⟨k, m, hm, hdec⟩
    rw [eval_trimCode, trimEnum] at hm
    simp only [Nat.unpair_pair, Part.mem_map_iff] at hm
    obtain ⟨s, hs, rfl⟩ := hm
    rw [Encodable.encodek] at hdec
    have hklt : k < (trimAccepted c d n s).length := by
      have := Nat.rfind_spec hs; simpa using this
    refine ⟨s, ?_⟩
    rw [← Option.some_injective _ hdec, List.getD_eq_getElem _ _ hklt]
    exact List.getElem_mem hklt
  · rintro ⟨s, hσ⟩
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hσ
    refine ⟨k, Encodable.encode σ, ?_, Encodable.encodek σ⟩
    rw [eval_trimCode, trimEnum]
    simp only [Nat.unpair_pair, Part.mem_map_iff]
    -- the least stage at which index `k` exists gives the same string, by prefix stability
    obtain ⟨t, htmem, hts⟩ :=
      Nat.rfind_min' (p := fun t ↦ decide (k < (trimAccepted c d n t).length)) (by simpa using hk)
    refine ⟨t, htmem, ?_⟩
    have htlt : k < (trimAccepted c d n t).length := by
      have := Nat.rfind_spec htmem; simpa using this
    rw [List.getD_eq_getElem _ _ htlt, (prefix_trimAccepted hts).getElem htlt]
    exact congrArg Encodable.encode hget

/-! ## The trimming contract

Trimming only removes cylinders (`denote_trim_subset`); every trimmed level obeys its budget
(`fairCoin_denote_trim_le`, `stageWeight_trim_le`); and if the source already obeys that
budget, trimming changes nothing (`denote_trim_of_le`).
-/

private theorem coe_pow_inv_two (k : ℕ) :
    (((2⁻¹ : ℚ≥0) ^ k : ℚ≥0) : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) ^ k := by
  rw [← ENNReal.coe_nnratCast]
  push_cast
  rfl

private theorem coe_le_coe_nnrat {a b : ℚ≥0} : ((a : ℝ≥0∞) ≤ (b : ℝ≥0∞)) ↔ a ≤ b := by
  rw [← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast, ENNReal.coe_le_coe]
  exact_mod_cast Iff.rfl

namespace UniformOpenCode

/-- Trim the family denoted by `e` at offset `d`: level `n` is `e`'s level `n + d`, greedily
truncated to the dyadic budget `2⁻⁽ⁿ⁺ᵈ⁾`. -/
noncomputable def trim (e : UniformOpenCode) (d : ℕ) : UniformOpenCode :=
  ⟨trimCode e.program d⟩

theorem mem_denote_trim {e : UniformOpenCode} {d n : ℕ} {x : Cantor} :
    x ∈ (e.trim d).denote n ↔ ∃ s, ∃ σ ∈ trimAccepted e.program d n s, x ∈ cylinder σ := by
  rw [mem_denote_iff_enumerates]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨s, hs⟩ := enumeratesString_trimCode.mp hσ
    exact ⟨s, σ, hs, hx⟩
  · rintro ⟨s, σ, hs, hx⟩
    exact ⟨σ, enumeratesString_trimCode.mpr ⟨s, hs⟩, hx⟩

theorem denote_trim_eq_iUnion (e : UniformOpenCode) (d n : ℕ) :
    (e.trim d).denote n = ⋃ s, cylinderUnion (trimAccepted e.program d n s).toFinset := by
  ext x
  rw [mem_denote_trim, Set.mem_iUnion]
  exact exists_congr fun s ↦ by simp [mem_cylinderUnion]

theorem monotone_trimCylinderUnion (e : UniformOpenCode) (d n : ℕ) :
    Monotone fun s ↦ cylinderUnion (trimAccepted e.program d n s).toFinset := by
  intro s t hst
  refine cylinderUnion_mono fun σ hσ ↦ ?_
  rw [List.mem_toFinset] at hσ ⊢
  exact (prefix_trimAccepted hst).subset hσ

/-- Trimming only removes cylinders. -/
theorem denote_trim_subset (e : UniformOpenCode) (d n : ℕ) :
    (e.trim d).denote n ⊆ e.denote (n + d) := by
  intro x hx
  obtain ⟨s, σ, hs, hxσ⟩ := mem_denote_trim.mp hx
  exact stageSet_subset_denote e (n + d) s (mem_stageSet.mpr
    ⟨σ, mem_stringStage_of_mem_trimAccepted hs, hxσ⟩)

/-- Every trimmed level obeys its budget. -/
theorem fairCoin_denote_trim_le (e : UniformOpenCode) (d n : ℕ) :
    fairCoin ((e.trim d).denote n) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + d) := by
  rw [denote_trim_eq_iUnion, (monotone_trimCylinderUnion e d n).measure_iUnion]
  refine iSup_le fun s ↦ ?_
  rw [fairCoin_cylinderUnion, ← coe_pow_inv_two]
  exact coe_le_coe_nnrat.mpr (finiteOpenWeight_trimAccepted_le e.program d n s)

/-- The exact rational form of the budget, on the trimmed code's own stages. -/
theorem stageWeight_trim_le (e : UniformOpenCode) (d n s : ℕ) :
    (e.trim d).stageWeight n s ≤ (2⁻¹ : ℚ≥0) ^ (n + d) := by
  have h := (fairCoin_denote_le_iff (e.trim d) n _).mp (fairCoin_denote_trim_le e d n) s
  rw [← coe_pow_inv_two] at h
  exact coe_le_coe_nnrat.mp h

/-- If the source already obeys the budget, trimming changes nothing. -/
theorem denote_trim_of_le (e : UniformOpenCode) (d n : ℕ)
    (h : fairCoin (e.denote (n + d)) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + d)) :
    (e.trim d).denote n = e.denote (n + d) := by
  have hstage : ∀ s, finiteOpenWeight (stringStage e.program (n + d) s)
      ≤ (2⁻¹ : ℚ≥0) ^ (n + d) := by
    intro s
    have hs := (fairCoin_denote_le_iff e (n + d) _).mp h s
    rw [← coe_pow_inv_two] at hs
    exact coe_le_coe_nnrat.mp hs
  rw [denote_trim_eq_iUnion, denote]
  refine Set.iUnion_congr fun s ↦ ?_
  rw [trimAccepted_eq_trace (hstage s), trace_toFinset]
  rfl

end UniformOpenCode

section Examples
-- trimming in action: the budget `2⁻¹` admits one of the two children, `2⁰ = 1` admits both
set_option linter.hashCommand false

#guard weightLe 1 [[true]] = true
#guard weightLe 1 [[true], [false]] = false
#guard accepted 1 [[true], [false]] = [[true]]
#guard accepted 0 [[true], [false]] = [[true], [false]]
#guard accepted 2 [[true], [true, false], [false, false]] = [[true, false]]

end Examples

end AlgorithmicRandomness
