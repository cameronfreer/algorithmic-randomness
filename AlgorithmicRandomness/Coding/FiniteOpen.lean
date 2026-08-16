/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.FiniteOpen
import AlgorithmicRandomness.Coding.NNRatCode
import AlgorithmicRandomness.Coding.Partrec

/-!
# Coded finite open sets

The executable presentation of finite unions of cylinders: everything runs on
`List BitString` and `ℕ`, never on `Finset` or `ℚ≥0`, because mathlib provides no
`Primcodable (Finset α)` and no `Primcodable ℚ≥0`. `Finset`, `finiteOpenWeight`, and `ℚ≥0`
appear only in correctness statements, never inside a function whose computability is
required. Filtering is written as folds because mathlib's `Primrec` list-filter and bounded
quantifiers are not parameterized in a second argument.

This layer has several independent consumers — trimming and Schnorr approximation among them —
so it sits below both.

The second half, in namespace `FiniteOpenCode`, is the intersection machinery: conditioning a
coded finite open set on a cylinder, which is again a coded finite open set with an exact
rational measure.
-/

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

/-! ## Computability of the weight layer -/

theorem primrec_prefixB : Primrec₂ prefixB :=
  primrec_decide (p := fun z : BitString × BitString ↦ List.take z.1.length z.2 = z.1)
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
        (primrec_decide
          (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)))))

/-- List membership, decided by index lookup: `Primrec` has no direct membership test. -/
private theorem primrec_memB :
    Primrec₂ fun (σ : BitString) (L : List BitString) ↦ decide (σ ∈ L) := by
  have h : Primrec fun z : BitString × List BitString ↦
      decide (@List.idxOf BitString instBEqOfDecidableEq z.1 z.2 < z.2.length) :=
    primrec_decide (Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
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
  primrec_decide (Primrec.nat_le.comp
    (Primrec.nat_mul.comp
      (primrec_natWeight.comp (primrec_maxLen.comp Primrec.snd) Primrec.snd)
      (primrec_natPow.comp (Primrec.const 2) Primrec.fst))
    (primrec_natPow.comp (Primrec.const 2) (primrec_maxLen.comp Primrec.snd)))

/-! ## Conditioning a coded finite open set on a cylinder -/

namespace FiniteOpenCode

/-! ## Meeting a cylinder -/

/-- The string naming `cylinder τ ∩ cylinder σ`, or `none` when the cylinders are disjoint. -/
def intersectString (τ σ : BitString) : Option BitString :=
  if prefixB τ σ then some σ else if prefixB σ τ then some τ else none

theorem cylinder_inter_cylinder (τ σ : BitString) :
    cylinder τ ∩ cylinder σ = (intersectString τ σ).elim ∅ cylinder := by
  unfold intersectString
  by_cases h1 : prefixB τ σ
  · rw [if_pos h1, Option.elim_some,
      Set.inter_eq_right.mpr (cylinder_anti ((prefixB_iff τ σ).mp h1))]
  · rw [if_neg h1]
    by_cases h2 : prefixB σ τ
    · rw [if_pos h2, Option.elim_some,
        Set.inter_eq_left.mpr (cylinder_anti ((prefixB_iff σ τ).mp h2))]
    · rw [if_neg h2, Option.elim_none, ← Set.disjoint_iff_inter_eq_empty]
      refine disjoint_cylinder_iff.mpr fun hc ↦ ?_
      rcases hc with h | h
      · exact h1 ((prefixB_iff τ σ).mpr h)
      · exact h2 ((prefixB_iff σ τ).mpr h)

/-- The strings naming `cylinderUnion L.toFinset ∩ cylinder σ`. -/
def intersectList (L : List BitString) (σ : BitString) : List BitString :=
  L.filterMap fun τ ↦ intersectString τ σ

theorem cylinderUnion_inter_cylinder (L : List BitString) (σ : BitString) :
    cylinderUnion L.toFinset ∩ cylinder σ = cylinderUnion (intersectList L σ).toFinset := by
  ext x
  simp only [Set.mem_inter_iff, mem_cylinderUnion, List.mem_toFinset, intersectList,
    List.mem_filterMap]
  constructor
  · rintro ⟨⟨τ, hτ, hxτ⟩, hxσ⟩
    have hmem : x ∈ cylinder τ ∩ cylinder σ := ⟨hxτ, hxσ⟩
    rw [cylinder_inter_cylinder] at hmem
    cases hm : intersectString τ σ with
    | none => rw [hm] at hmem; exact absurd hmem (Set.notMem_empty x)
    | some ρ => exact ⟨ρ, ⟨τ, hτ, hm⟩, by rw [hm] at hmem; exact hmem⟩
  · rintro ⟨ρ, ⟨τ, hτ, hm⟩, hxρ⟩
    have : x ∈ cylinder τ ∩ cylinder σ := by
      rw [cylinder_inter_cylinder, hm]; exact hxρ
    exact ⟨⟨τ, hτ, this.1⟩, this.2⟩

/-! ## The exact rational measure -/

/-- The exact measure of `cylinderUnion F ∩ cylinder σ`, semantically. -/
noncomputable def capWeight (F : Finset BitString) (σ : BitString) : ℚ≥0 :=
  finiteOpenWeight (intersectList F.toList σ).toFinset

theorem intersectList_toFinset_congr {L L' : List BitString} (h : ∀ τ, τ ∈ L ↔ τ ∈ L')
    (σ : BitString) : (intersectList L σ).toFinset = (intersectList L' σ).toFinset := by
  ext ρ
  simp only [List.mem_toFinset, intersectList, List.mem_filterMap]
  exact ⟨fun ⟨τ, hτ, hm⟩ ↦ ⟨τ, (h τ).mp hτ, hm⟩, fun ⟨τ, hτ, hm⟩ ↦ ⟨τ, (h τ).mpr hτ, hm⟩⟩

theorem capWeight_toFinset (L : List BitString) (σ : BitString) :
    capWeight L.toFinset σ = finiteOpenWeight (intersectList L σ).toFinset := by
  rw [capWeight,
    intersectList_toFinset_congr (L := L.toFinset.toList) (L' := L) (fun τ ↦ by simp) σ]

theorem fairCoin_cylinderUnion_inter_cylinder (L : List BitString) (σ : BitString) :
    fairCoin (cylinderUnion L.toFinset ∩ cylinder σ) = (capWeight L.toFinset σ : ℝ≥0∞) := by
  rw [cylinderUnion_inter_cylinder, fairCoin_cylinderUnion, capWeight_toFinset]

/-! ## The executable version -/

/-- The coded exact measure of `cylinderUnion L.toFinset ∩ cylinder σ`, computed entirely in
`ℕ`: numerator `natWeight`, denominator the matching power of two. -/
def capWeightCode (L : List BitString) (σ : BitString) : ℕ :=
  Nat.pair (natWeight (maxLen (intersectList L σ)) (intersectList L σ))
    (2 ^ maxLen (intersectList L σ) - 1)

theorem value_capWeightCode (L : List BitString) (σ : BitString) :
    NNRatCode.value (capWeightCode L σ) = capWeight L.toFinset σ := by
  rw [capWeightCode, NNRatCode.value_pair, Nat.sub_add_cancel Nat.one_le_two_pow,
    capWeight_toFinset, natWeight_cast]
  push_cast
  rw [mul_comm, mul_div_assoc,
    div_self (by positivity : ((2 : ℚ≥0) ^ maxLen (intersectList L σ)) ≠ 0), mul_one]

theorem primrec_intersectString : Primrec₂ intersectString := by
  unfold intersectString
  refine Primrec.ite (Primrec.eq.comp primrec_prefixB (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) ?_
  exact Primrec.ite
    (Primrec.eq.comp (primrec_prefixB.comp Primrec.snd Primrec.fst) (Primrec.const true))
    (Primrec.option_some.comp Primrec.fst) (Primrec.const none)

theorem primrec_intersectList : Primrec₂ intersectList :=
  Primrec.listFilterMap Primrec.fst
    (primrec_intersectString.comp Primrec.snd (Primrec.snd.comp Primrec.fst))

theorem primrec_capWeightCode : Primrec₂ capWeightCode := by
  have hm : Primrec fun z : List BitString × BitString ↦ intersectList z.1 z.2 :=
    primrec_intersectList
  have hlen : Primrec fun z : List BitString × BitString ↦ maxLen (intersectList z.1 z.2) :=
    primrec_maxLen.comp hm
  refine Primrec₂.natPair.comp (primrec_natWeight.comp hlen hm) ?_
  exact Primrec.nat_sub.comp
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) hlen) (Primrec.const 1)

/-! ## The finite-open difference

The fresh part of an increasing pair of finite open sets, as an explicit prefix-free family. This
is what an append-only accounting must emit: successive *minimized* stages cannot be compared
directly, because a shorter cylinder can replace earlier longer ones and the historical weights
then overcount.

The construction refines every member of `new` to the common length `maxLen (new ++ old)` and
keeps the extensions not already covered by `old`. At one fixed length the covering dichotomy is
exact — a member of `old` is a prefix of a point of `[ρ]` exactly when it is a prefix of `ρ` — and
prefix-freeness is automatic, since distinct strings of equal length are incomparable.

The result is not minimal, and can be exponentially larger than necessary. Nothing downstream asks
for minimality: what is needed is the exact weight identity below, and refinement is what makes
every step a membership computation rather than a normal-form argument.
-/

/-- All extensions of `σ` to length `L`. -/
def extendTo (L : ℕ) (σ : BitString) : List BitString :=
  (BitString.wordsOfLength (L - σ.length)).map (σ ++ ·)

theorem mem_extendTo {L : ℕ} {σ ρ : BitString} (h : σ.length ≤ L) :
    ρ ∈ extendTo L σ ↔ σ <+: ρ ∧ ρ.length = L := by
  rw [extendTo, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, rfl⟩, ?_⟩
    rw [List.length_append, BitString.length_of_mem_wordsOfLength hw]
    omega
  · rintro ⟨⟨w, rfl⟩, hlen⟩
    refine ⟨w, ?_, rfl⟩
    rw [List.length_append] at hlen
    have : w.length = L - σ.length := by omega
    rw [← this]
    exact BitString.mem_wordsOfLength_length w

/-- Some member of `L` is a prefix of `ρ`. -/
def coveredBy (L : List BitString) (ρ : BitString) : Bool :=
  L.foldr (fun σ b ↦ b || prefixB σ ρ) false

theorem coveredBy_iff {L : List BitString} {ρ : BitString} :
    coveredBy L ρ = true ↔ ∃ σ ∈ L, σ <+: ρ := by
  rw [coveredBy]
  induction L with
  | nil => simp
  | cons μ L ih =>
    rw [List.foldr_cons]
    simp only [Bool.or_eq_true, ih, prefixB_iff, List.mem_cons]
    constructor
    · rintro (⟨σ, hσ, hp⟩ | hp)
      · exact ⟨σ, Or.inr hσ, hp⟩
      · exact ⟨μ, Or.inl rfl, hp⟩
    · rintro ⟨σ, rfl | hσ, hp⟩
      · exact Or.inr hp
      · exact Or.inl ⟨σ, hσ, hp⟩

/-- The fresh part of `new` beyond `old`: a prefix-free family at one common length. -/
def difference (new old : List BitString) : List BitString :=
  (new.flatMap (extendTo (maxLen (new ++ old)))).filterMap fun ρ ↦
    if coveredBy old ρ then none else some ρ

theorem mem_difference {new old : List BitString} {ρ : BitString} :
    ρ ∈ difference new old ↔
      (∃ σ ∈ new, σ <+: ρ) ∧ ρ.length = maxLen (new ++ old) ∧ coveredBy old ρ = false := by
  rw [difference, List.mem_filterMap]
  constructor
  · rintro ⟨μ, hμ, hsome⟩
    by_cases hc : coveredBy old μ = true
    · rw [if_pos hc] at hsome; exact absurd hsome (by simp)
    · rw [if_neg hc, Option.some_inj] at hsome
      subst hsome
      rw [List.mem_flatMap] at hμ
      obtain ⟨σ, hσ, hmem⟩ := hμ
      obtain ⟨hpre, hlen⟩ := (mem_extendTo (length_le_maxLen (by simp [hσ]))).mp hmem
      exact ⟨⟨σ, hσ, hpre⟩, hlen, by simpa using hc⟩
  · rintro ⟨⟨σ, hσ, hpre⟩, hlen, hc⟩
    refine ⟨ρ, List.mem_flatMap.mpr ⟨σ, hσ, ?_⟩, by rw [if_neg (by simp [hc])]⟩
    exact (mem_extendTo (length_le_maxLen (by simp [hσ]))).mpr ⟨hpre, hlen⟩

theorem length_of_mem_difference {new old : List BitString} {ρ : BitString}
    (h : ρ ∈ difference new old) : ρ.length = maxLen (new ++ old) := (mem_difference.mp h).2.1

/-- **Prefix-free**, because everything emitted sits at one length. -/
theorem prefixFree_difference (new old : List BitString) :
    PrefixFree ((difference new old).toFinset : Set BitString) := by
  rw [prefixFree_iff]
  intro σ hσ τ hτ hpre
  rw [Finset.mem_coe, List.mem_toFinset] at hσ hτ
  exact hpre.eq_of_length
    ((length_of_mem_difference hσ).trans (length_of_mem_difference hτ).symm)

/-- **The semantic contract.** -/
theorem cylinderUnion_difference (new old : List BitString) :
    cylinderUnion (difference new old).toFinset
      = cylinderUnion new.toFinset \ cylinderUnion old.toFinset := by
  ext x
  rw [mem_cylinderUnion, Set.mem_sdiff, mem_cylinderUnion, mem_cylinderUnion]
  constructor
  · rintro ⟨ρ, hρ, hx⟩
    rw [List.mem_toFinset] at hρ
    obtain ⟨⟨σ, hσ, hpre⟩, hlen, hc⟩ := mem_difference.mp hρ
    refine ⟨⟨σ, List.mem_toFinset.mpr hσ, cylinder_subset_cylinder_iff.mpr hpre hx⟩, ?_⟩
    rintro ⟨τ, hτ, hxτ⟩
    rw [List.mem_toFinset] at hτ
    have hτL : τ.length ≤ ρ.length := by
      rw [hlen]
      exact length_le_maxLen (by simp [hτ])
    have hτρ : τ <+: ρ := by
      rw [← initSeg_of_mem_cylinder hx, ← initSeg_of_mem_cylinder hxτ]
      exact initSeg_prefix_of_le hτL
    rw [← Bool.not_eq_true] at hc
    exact hc (coveredBy_iff.mpr ⟨τ, hτ, hτρ⟩)
  · rintro ⟨⟨σ, hσ, hx⟩, hnot⟩
    rw [List.mem_toFinset] at hσ
    set L := maxLen (new ++ old) with hL
    have hσL : σ.length ≤ L := length_le_maxLen (by simp [hσ])
    refine ⟨initSeg x L, List.mem_toFinset.mpr (mem_difference.mpr ⟨⟨σ, hσ, ?_⟩, ?_, ?_⟩),
      mem_cylinder_initSeg x L⟩
    · rw [← initSeg_of_mem_cylinder hx]
      exact initSeg_prefix_of_le hσL
    · exact length_initSeg x L
    · rw [← Bool.not_eq_true, ← ne_eq]
      intro hc
      obtain ⟨τ, hτ, hτρ⟩ := coveredBy_iff.mp hc
      exact hnot ⟨τ, List.mem_toFinset.mpr hτ,
        cylinder_subset_cylinder_iff.mpr hτρ (mem_cylinder_initSeg x L)⟩

/-- **The weight identity.** The old set and the fresh part are disjoint and cover the new set, so
their exact rational weights add. -/
theorem weight_add_difference {new old : List BitString}
    (h : cylinderUnion old.toFinset ⊆ cylinderUnion new.toFinset) :
    finiteOpenWeight old.toFinset + totalWeight (difference new old).toFinset
      = finiteOpenWeight new.toFinset := by
  have hdisj : Disjoint (cylinderUnion old.toFinset)
      (cylinderUnion (difference new old).toFinset) := by
    rw [cylinderUnion_difference]
    exact Set.disjoint_sdiff_right
  have hunion : cylinderUnion old.toFinset ∪ cylinderUnion (difference new old).toFinset
      = cylinderUnion new.toFinset := by
    rw [cylinderUnion_difference, Set.union_sdiff_cancel h]
  have hmeas : fairCoin (cylinderUnion old.toFinset)
      + fairCoin (cylinderUnion (difference new old).toFinset)
      = fairCoin (cylinderUnion new.toFinset) := by
    rw [← hunion, measure_union hdisj (measurableSet_cylinderUnion _)]
  rw [fairCoin_cylinderUnion old.toFinset, fairCoin_cylinderUnion new.toFinset,
    fairCoin_cylinderUnion_of_prefixFree (prefixFree_difference new old)] at hmeas
  rw [← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast,
    ← ENNReal.coe_add] at hmeas
  exact_mod_cast hmeas

theorem primrec_extendTo : Primrec₂ extendTo := by
  refine Primrec.list_map
    (BitString.primrec_wordsOfLength.comp
      (Primrec.nat_sub.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))) ?_
  exact (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

theorem primrec_coveredBy : Primrec₂ coveredBy := by
  have h : Primrec₂ fun (z : List BitString × BitString) (p : BitString × Bool) ↦
      p.2 || prefixB p.1 z.2 :=
    (Primrec.or.comp (Primrec.snd.comp Primrec.snd)
      (primrec_prefixB.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.list_foldr Primrec.fst
    (Primrec.const (α := List BitString × BitString) false) h

theorem primrec_difference : Primrec₂ difference := by
  have hlen : Primrec fun z : List BitString × List BitString ↦ maxLen (z.1 ++ z.2) :=
    primrec_maxLen.comp (Primrec.list_append.comp Primrec.fst Primrec.snd)
  refine Primrec.listFilterMap
    (Primrec.list_flatMap Primrec.fst
      ((primrec_extendTo.comp (hlen.comp Primrec.fst) Primrec.snd).to₂)) ?_
  refine Primrec.ite
    (Primrec.eq.comp (primrec_coveredBy.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const true))
    (Primrec.const none) (Primrec.option_some.comp Primrec.snd)

end FiniteOpenCode

end AlgorithmicRandomness
