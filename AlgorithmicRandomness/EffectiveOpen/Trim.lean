/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
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

/-! ## The list-only weight layer -/

/-- List-only prefix test, phrased via `take` so it is primitive recursive. -/
def prefixB (τ σ : BitString) : Bool := decide (σ.take τ.length = τ)

/-- `σ` has no proper prefix among the members of `L`, as a fold. -/
def noProperPrefixIn (L : List BitString) (σ : BitString) : Bool :=
  L.foldr (fun τ b ↦ b && (!prefixB τ σ || decide (τ = σ))) true

/-- List-only prefix-free normalizer: dedup, then keep the prefix-minimal members. -/
def minimalNodup (L : List BitString) : List BitString :=
  L.dedup.foldr (fun σ acc ↦ if noProperPrefixIn L σ then σ :: acc else acc) []

/-- A length bound for the members of `L`. -/
def maxLen (L : List BitString) : ℕ := L.foldr (fun σ m ↦ max σ.length m) 0

/-- Common-denominator numerator for the exact weight of `L`. -/
def natWeight (D : ℕ) (L : List BitString) : ℕ :=
  (minimalNodup L).foldr (fun σ w ↦ 2 ^ (D - σ.length) + w) 0

/-- Decides `finiteOpenWeight L.toFinset ≤ 2⁻ᵇ` entirely in `ℕ`. -/
def weightLe (b : ℕ) (L : List BitString) : Bool :=
  decide (natWeight (maxLen L) L * 2 ^ b ≤ 2 ^ maxLen L)

theorem prefixB_iff (τ σ : BitString) : prefixB τ σ = true ↔ τ <+: σ := by
  rw [prefixB, decide_eq_true_iff, List.prefix_iff_eq_take, eq_comm]

theorem noProperPrefixIn_iff (L : List BitString) (σ : BitString) :
    noProperPrefixIn L σ = true ↔ ∀ τ ∈ L, τ <+: σ → τ = σ := by
  have key : ∀ τ : BitString, ((!prefixB τ σ || decide (τ = σ)) = true) ↔ (τ <+: σ → τ = σ) := by
    intro τ
    cases hb : prefixB τ σ with
    | false =>
      have hnp : ¬τ <+: σ := by rw [← prefixB_iff, hb]; simp
      simp [hnp]
    | true =>
      have hp : τ <+: σ := (prefixB_iff τ σ).mp hb
      simp [hp]
  induction L with
  | nil => simp [noProperPrefixIn]
  | cons a t ih =>
    have hstep : noProperPrefixIn (a :: t) σ
        = (noProperPrefixIn t σ && (!prefixB a σ || decide (a = σ))) := rfl
    rw [hstep, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩ τ hτ hpre
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact (key _).mp h2 hpre
      · exact ih.mp h1 τ hτ hpre
    · intro h
      exact ⟨ih.mpr fun τ hτ ↦ h τ (List.mem_cons_of_mem _ hτ),
        (key a).mpr (h a List.mem_cons_self)⟩

/-- The `foldr`-with-`ite` in `minimalNodup` is a `List.filter`. -/
private theorem foldr_ite_eq_filter (p : BitString → Bool) (l : List BitString) :
    l.foldr (fun σ acc ↦ if p σ then σ :: acc else acc) [] = l.filter p := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.foldr_cons, ih, List.filter_cons]

theorem minimalNodup_eq_filter (L : List BitString) :
    minimalNodup L = L.dedup.filter (noProperPrefixIn L) :=
  foldr_ite_eq_filter _ _

theorem minimalNodup_nodup (L : List BitString) : (minimalNodup L).Nodup := by
  rw [minimalNodup_eq_filter]
  exact (L.nodup_dedup).filter _

theorem mem_minimalNodup {L : List BitString} {σ : BitString} :
    σ ∈ minimalNodup L ↔ σ ∈ L ∧ ∀ τ ∈ L, τ <+: σ → τ = σ := by
  rw [minimalNodup_eq_filter, List.mem_filter, List.mem_dedup, noProperPrefixIn_iff]

theorem minimalNodup_toFinset (L : List BitString) :
    (minimalNodup L).toFinset = minimize L.toFinset := by
  ext σ
  simp [List.mem_toFinset, mem_minimalNodup, mem_minimize]

theorem length_le_maxLen {L : List BitString} {σ : BitString} (h : σ ∈ L) :
    σ.length ≤ maxLen L := by
  induction L with
  | nil => simp at h
  | cons a t ih =>
    rw [maxLen, List.foldr_cons, ← maxLen]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem natWeight_eq_sum (D : ℕ) (L : List BitString) :
    natWeight D L = ((minimalNodup L).map fun σ ↦ 2 ^ (D - σ.length)).sum := by
  rw [natWeight]
  generalize minimalNodup L = M
  induction M with
  | nil => rfl
  | cons a t ih => rw [List.foldr_cons, ih, List.map_cons, List.sum_cons]

private theorem cast_two_pow_sub {D l : ℕ} (h : l ≤ D) :
    ((2 : ℚ≥0) ^ (D - l)) = 2 ^ D * (2⁻¹ : ℚ≥0) ^ l := by
  rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero l (two_ne_zero)), ← pow_add,
    Nat.sub_add_cancel h]

private theorem sum_map_cast (D : ℕ) :
    ∀ M : List BitString, (∀ σ ∈ M, σ.length ≤ D) →
      ((((M.map fun σ ↦ 2 ^ (D - σ.length)).sum : ℕ) : ℚ≥0))
        = 2 ^ D * (M.map BitString.weight).sum := by
  intro M
  induction M with
  | nil => simp
  | cons a t ih =>
    intro h
    have ha : a.length ≤ D := h a List.mem_cons_self
    have ht : ∀ σ ∈ t, σ.length ≤ D := fun σ hσ ↦ h σ (List.mem_cons_of_mem _ hσ)
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih ht, mul_add]
    congr 1
    rw [Nat.cast_pow, Nat.cast_ofNat, BitString.weight, cast_two_pow_sub ha]

theorem natWeight_cast (L : List BitString) :
    ((natWeight (maxLen L) L : ℕ) : ℚ≥0) = 2 ^ maxLen L * finiteOpenWeight L.toFinset := by
  have hlen : ∀ σ ∈ minimalNodup L, σ.length ≤ maxLen L := fun σ hσ ↦
    length_le_maxLen (mem_minimalNodup.mp hσ).1
  rw [natWeight_eq_sum, finiteOpenWeight, ← minimalNodup_toFinset, totalWeight,
    List.sum_toFinset _ (minimalNodup_nodup L)]
  exact sum_map_cast _ _ hlen

/-- The bridge between the executable `ℕ` decision and the exact `ℚ≥0` weight API. -/
theorem weightLe_iff (b : ℕ) (L : List BitString) :
    weightLe b L = true ↔ finiteOpenWeight L.toFinset ≤ (2⁻¹ : ℚ≥0) ^ b := by
  set D := maxLen L with hD
  set W := finiteOpenWeight L.toFinset with hW
  have hcast : ((natWeight D L : ℕ) : ℚ≥0) = 2 ^ D * W := natWeight_cast L
  have hpow : ((2 : ℚ≥0)⁻¹) ^ b * 2 ^ b = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (two_ne_zero), one_pow]
  have hnat : weightLe b L = true ↔ ((natWeight D L : ℕ) : ℚ≥0) * 2 ^ b ≤ 2 ^ D := by
    rw [weightLe, decide_eq_true_iff, ← hD]
    constructor
    · intro h
      have := (Nat.cast_le (α := ℚ≥0)).mpr h
      push_cast at this
      exact this
    · intro h
      have : ((natWeight D L * 2 ^ b : ℕ) : ℚ≥0) ≤ ((2 ^ D : ℕ) : ℚ≥0) := by push_cast; exact h
      exact_mod_cast this
  rw [hnat, hcast]
  have h2D : (0 : ℚ≥0) < 2 ^ D := by positivity
  have h2b : (0 : ℚ≥0) < 2 ^ b := by positivity
  calc 2 ^ D * W * 2 ^ b ≤ 2 ^ D
      ↔ 2 ^ D * (W * 2 ^ b) ≤ 2 ^ D * ((2⁻¹ : ℚ≥0) ^ b * 2 ^ b) := by
        rw [hpow, mul_one, mul_assoc]
    _ ↔ W * 2 ^ b ≤ (2⁻¹ : ℚ≥0) ^ b * 2 ^ b := mul_le_mul_iff_right₀ h2D
    _ ↔ W ≤ (2⁻¹ : ℚ≥0) ^ b := mul_le_mul_iff_left₀ h2b

/-! ## The append-only discovery trace -/

/-- Everything resolved at stage `s`, in ascending input order. -/
def emitAll (c : Code) (n s : ℕ) : List BitString :=
  (List.range (s + 1)).filterMap fun k ↦ stringOut c s (Nat.pair n k)

theorem emitAll_toFinset (c : Code) (n s : ℕ) : (emitAll c n s).toFinset = stringStage c n s :=
  rfl

/-- The append-only chronology of discoveries: ordered by stage, then by input. -/
def trace (c : Code) (n s : ℕ) : List BitString :=
  Nat.rec (emitAll c n 0) (fun s' IH ↦ IH ++ emitAll c n (s' + 1)) s

@[simp] theorem trace_zero (c : Code) (n : ℕ) : trace c n 0 = emitAll c n 0 := rfl

@[simp] theorem trace_succ (c : Code) (n s : ℕ) :
    trace c n (s + 1) = trace c n s ++ emitAll c n (s + 1) := rfl

theorem trace_prefix_succ (c : Code) (n s : ℕ) : trace c n s <+: trace c n (s + 1) :=
  ⟨emitAll c n (s + 1), rfl⟩

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
  | zero => rw [trace_zero, emitAll_toFinset]
  | succ s ih =>
    rw [trace_succ, List.toFinset_append, ih, emitAll_toFinset]
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

private theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- `PrimrecPred` bundles a `Decidable` instance existentially; this extracts the underlying
`Bool`-valued primitive recursive function, which is what the fold combinators consume. -/
private theorem toBool {α : Type*} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (h : PrimrecPred p) : Primrec fun a ↦ decide (p a) :=
  primrecPred_iff_primrec_decide.mp h

theorem primrec_emitAll : Primrec fun z : (Code × ℕ) × ℕ ↦ emitAll z.1.1 z.1.2 z.2 := by
  unfold emitAll
  refine Primrec.listFilterMap
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd (α := Code × ℕ) (β := ℕ)))) ?_
  exact primrec_stringOut.comp
    ((((Primrec.fst.comp Primrec.fst).comp Primrec.fst).pair
      (Primrec.snd.comp Primrec.fst)).pair
      (Primrec₂.natPair.comp ((Primrec.snd.comp Primrec.fst).comp Primrec.fst) Primrec.snd))

theorem primrec_trace : Primrec fun z : (Code × ℕ) × ℕ ↦ trace z.1.1 z.1.2 z.2 := by
  unfold trace
  refine (Primrec.nat_rec (α := Code × ℕ)
    (f := fun z : Code × ℕ ↦ emitAll z.1 z.2 0)
    (g := fun (z : Code × ℕ) (p : ℕ × List BitString) ↦ p.2 ++ emitAll z.1 z.2 (p.1 + 1))
    ?_ ?_).comp Primrec.fst Primrec.snd
  · exact primrec_emitAll.comp (Primrec.id.pair (Primrec.const 0))
  · exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (primrec_emitAll.comp (Primrec.fst.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))))

theorem primrec_prefixB : Primrec₂ prefixB :=
  toBool (p := fun z : BitString × BitString ↦ List.take z.1.length z.2 = z.1)
    (Primrec.eq.comp
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd) Primrec.fst)

theorem primrec_noProperPrefixIn : Primrec₂ noProperPrefixIn :=
  Primrec.list_foldr (β := BitString) (σ := Bool)
    (f := fun z : List BitString × BitString ↦ z.1)
    (g := fun _ ↦ true)
    (h := fun z p ↦ p.2 && (!prefixB p.1 z.2 || decide (p.1 = z.2)))
    Primrec.fst (Primrec.const true)
    (Primrec.and.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.or.comp
        (Primrec.not.comp
          (primrec_prefixB.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)))
        (toBool (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)))))

/-- List membership, decided by index lookup: `Primrec` has no direct membership test. -/
private theorem primrec_memB :
    Primrec₂ fun (σ : BitString) (L : List BitString) ↦ decide (σ ∈ L) := by
  have h : Primrec fun z : BitString × List BitString ↦
      decide (@List.idxOf BitString instBEqOfDecidableEq z.1 z.2 < z.2.length) :=
    toBool (Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd))
  exact h.of_eq fun z ↦ by simp [List.idxOf_lt_length_iff]

theorem primrec_dedup : Primrec (List.dedup : List BitString → List BitString) := by
  have h : Primrec fun L : List BitString ↦
      List.rec (motive := fun _ ↦ List BitString) []
        (fun a l IH ↦ if (decide (a ∈ l)) = true then IH else a :: IH) L :=
    Primrec.list_rec (β := BitString) (σ := List BitString)
      (f := fun L : List BitString ↦ L) (g := fun _ ↦ [])
      (h := fun _ p ↦ if (decide (p.1 ∈ p.2.1)) = true then p.2.2 else p.1 :: p.2.2)
      Primrec.id (Primrec.const [])
      (Primrec.ite
        (Primrec.eq.comp
          (primrec_memB.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.const true))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  refine h.of_eq fun L ↦ ?_
  induction L with
  | nil => rfl
  | cons a l ih =>
    by_cases hmem : a ∈ l
    · rw [List.dedup_cons_of_mem hmem, ← ih]
      simp [hmem]
    · rw [List.dedup_cons_of_notMem hmem, ← ih]
      simp [hmem]

theorem primrec_minimalNodup : Primrec minimalNodup :=
  Primrec.list_foldr (β := BitString) (σ := List BitString)
    (f := fun L : List BitString ↦ L.dedup) (g := fun _ ↦ [])
    (h := fun L p ↦ if noProperPrefixIn L p.1 = true then p.1 :: p.2 else p.2)
    primrec_dedup (Primrec.const [])
    (Primrec.ite
      (Primrec.eq.comp
        (primrec_noProperPrefixIn.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.const true))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_maxLen : Primrec maxLen :=
  Primrec.list_foldr (β := BitString) (σ := ℕ)
    (f := fun L : List BitString ↦ L) (g := fun _ ↦ 0)
    (h := fun _ p ↦ max p.1.length p.2)
    Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_natWeight : Primrec₂ natWeight :=
  Primrec.list_foldr (β := BitString) (σ := ℕ)
    (f := fun z : ℕ × List BitString ↦ minimalNodup z.2) (g := fun _ ↦ 0)
    (h := fun z p ↦ 2 ^ (z.1 - p.1.length) + p.2)
    (primrec_minimalNodup.comp Primrec.snd) (Primrec.const 0)
    (Primrec.nat_add.comp
      (primrec_natPow.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd))

theorem primrec_weightLe : Primrec₂ weightLe :=
  toBool (Primrec.nat_le.comp
    (Primrec.nat_mul.comp
      (primrec_natWeight.comp (primrec_maxLen.comp Primrec.snd) Primrec.snd)
      (primrec_natPow.comp (Primrec.const 2) Primrec.fst))
    (primrec_natPow.comp (Primrec.const 2) (primrec_maxLen.comp Primrec.snd)))

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
  · exact Computable₂.partrec₂ (toBool (Primrec.nat_lt.comp
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
