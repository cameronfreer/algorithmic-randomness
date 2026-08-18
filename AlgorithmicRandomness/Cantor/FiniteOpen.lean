/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.FairCoin
import Mathlib.Data.NNRat.BigOperators

/-!
# Finite open sets and exact dyadic measures

A finite set `F : Finset BitString` names the finite open set `cylinderUnion F`. This file
provides the prefix-free normalization `minimize F` — delete every string properly extending
another member — and exact `ℚ≥0` weights, and proves that they compute the fair-coin measure:

* `fairCoin_cylinderUnion_of_prefixFree`: for a prefix-free family the measure is the cast of
  `totalWeight F`, the sum of the cylinder weights `2⁻¹ ^ σ.length`;
* `fairCoin_cylinderUnion`: for an arbitrary family the measure is the cast of
  `finiteOpenWeight F := totalWeight (minimize F)`.

`finiteOpenWeight` is the executable exact measure that later trimming constructions consume.
The section ends with the finite Kraft inequality `totalWeight_le_one_of_prefixFree`.
-/

open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## Finite unions of cylinders -/

/-- The finite open set named by a finite set of strings. -/
def cylinderUnion (F : Finset BitString) : Set Cantor := ⋃ σ ∈ F, cylinder σ

@[simp]
theorem mem_cylinderUnion {F : Finset BitString} {x : Cantor} :
    x ∈ cylinderUnion F ↔ ∃ σ ∈ F, x ∈ cylinder σ := by
  simp [cylinderUnion]

@[simp]
theorem cylinderUnion_empty : cylinderUnion ∅ = (∅ : Set Cantor) := by
  simp [cylinderUnion]

theorem cylinderUnion_mono {F G : Finset BitString} (h : F ⊆ G) :
    cylinderUnion F ⊆ cylinderUnion G := by
  intro x hx
  rw [mem_cylinderUnion] at hx ⊢
  obtain ⟨σ, hσ, hxσ⟩ := hx
  exact ⟨σ, h hσ, hxσ⟩

theorem measurableSet_cylinderUnion (F : Finset BitString) :
    MeasurableSet (cylinderUnion F) :=
  F.measurableSet_biUnion fun σ _ ↦ measurableSet_cylinder σ

/-! ## Prefix-free families -/

/-- A set of strings is prefix-free if distinct members are incompatible: it is an antichain
in the prefix order. Stated for arbitrary sets; finite families use the `Finset` coercion. -/
def PrefixFree (S : Set BitString) : Prop :=
  S.Pairwise fun σ τ ↦ ¬BitString.Compatible σ τ

/-- Prefix-freeness on a finite family is decidable (and executable). -/
instance (F : Finset BitString) : Decidable (PrefixFree (F : Set BitString)) :=
  decidable_of_iff (∀ σ ∈ F, ∀ τ ∈ F, σ ≠ τ → ¬BitString.Compatible σ τ) (by
    simp [PrefixFree, Set.Pairwise])

/-- The antichain formulation is equivalent to "no member is a proper prefix of another". -/
theorem prefixFree_iff {S : Set BitString} :
    PrefixFree S ↔ ∀ σ ∈ S, ∀ τ ∈ S, σ <+: τ → σ = τ := by
  constructor
  · intro h σ hσ τ hτ hpre
    by_contra hne
    exact h hσ hτ hne (Or.inl hpre)
  · rintro h σ hσ τ hτ hne (hpre | hpre)
    · exact hne (h σ hσ τ hτ hpre)
    · exact hne (h τ hτ σ hσ hpre).symm

/-- Prefix-free families have pairwise disjoint cylinders: the hand-off to the measure API. -/
theorem PrefixFree.pairwiseDisjoint_cylinder {S : Set BitString} (h : PrefixFree S) :
    S.PairwiseDisjoint cylinder :=
  fun _ hσ _ hτ hne ↦ disjoint_cylinder_iff.mpr (h hσ hτ hne)

/-! ## Prefix-free normalization -/

/-- Normalize a finite family by deleting every string that properly extends another member:
keep `σ` iff the only prefix of `σ` in `F` is `σ` itself. Executable. -/
def minimize (F : Finset BitString) : Finset BitString :=
  F.filter fun σ ↦ ∀ τ ∈ F, τ <+: σ → τ = σ

@[simp]
theorem mem_minimize {F : Finset BitString} {σ : BitString} :
    σ ∈ minimize F ↔ σ ∈ F ∧ ∀ τ ∈ F, τ <+: σ → τ = σ := by
  simp [minimize]

theorem minimize_subset (F : Finset BitString) : minimize F ⊆ F :=
  Finset.filter_subset _ F

theorem prefixFree_minimize (F : Finset BitString) :
    PrefixFree (minimize F : Set BitString) := by
  rw [prefixFree_iff]
  intro σ hσ τ hτ hpre
  rw [Finset.mem_coe, mem_minimize] at hσ hτ
  exact hτ.2 σ hσ.1 hpre

theorem minimize_eq_self_iff {F : Finset BitString} :
    minimize F = F ↔ PrefixFree (F : Set BitString) := by
  rw [prefixFree_iff]
  constructor
  · intro h σ hσ τ hτ hpre
    rw [Finset.mem_coe, ← h, mem_minimize] at hτ
    exact hτ.2 σ (by rwa [Finset.mem_coe] at hσ) hpre
  · intro h
    refine Finset.Subset.antisymm (minimize_subset F) fun σ hσ ↦ ?_
    rw [mem_minimize]
    exact ⟨hσ, fun τ hτ hpre ↦ h τ hτ σ hσ hpre⟩

theorem minimize_idem (F : Finset BitString) : minimize (minimize F) = minimize F :=
  minimize_eq_self_iff.mpr (prefixFree_minimize F)

/-- Normalization does not change the named open set. -/
theorem cylinderUnion_minimize (F : Finset BitString) :
    cylinderUnion (minimize F) = cylinderUnion F := by
  refine Set.Subset.antisymm (cylinderUnion_mono (minimize_subset F)) fun x hx ↦ ?_
  rw [mem_cylinderUnion] at hx ⊢
  obtain ⟨σ, hσF, hxσ⟩ := hx
  -- pass to a minimum-length prefix of `σ` in `F`; it is necessarily in `minimize F`
  obtain ⟨τ, hτmem, hτmin⟩ := (F.filter fun τ ↦ τ <+: σ).exists_min_image
    (fun τ ↦ τ.length) ⟨σ, Finset.mem_filter.mpr ⟨hσF, List.prefix_refl σ⟩⟩
  rw [Finset.mem_filter] at hτmem
  obtain ⟨hτF, hτσ⟩ := hτmem
  refine ⟨τ, mem_minimize.mpr ⟨hτF, fun ρ hρF hρτ ↦ ?_⟩, cylinder_anti hτσ hxσ⟩
  have hρσ : ρ <+: σ := hρτ.trans hτσ
  have hlen := hτmin ρ (Finset.mem_filter.mpr ⟨hρF, hρσ⟩)
  exact hρτ.eq_of_length (le_antisymm hρτ.length_le hlen)

section Examples
-- executable acceptance checks for the normalizer; `#`-commands are fine outside mathlib
set_option linter.hashCommand false

#guard minimize {[true], [true, false]} = {[true]}
#guard minimize {[true, false], [false], [true]} = {[false], [true]}
#guard decide (PrefixFree ({[false], [true, false]} : Finset BitString))

end Examples

/-! ## Exact weights -/

/-! ### Casting exact weights into the measure

Weights are exact in `ℚ≥0` and measures live in `ℝ≥0∞`, so every measure bound crosses once. These
two bridges are that crossing; they are stated here rather than repeated at each use site. -/

theorem coe_pow_inv_two (k : ℕ) :
    (((2⁻¹ : ℚ≥0) ^ k : ℚ≥0) : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) ^ k := by
  rw [← ENNReal.coe_nnratCast]
  push_cast
  rfl

theorem coe_le_coe_nnrat {a b : ℚ≥0} : ((a : ℝ≥0∞) ≤ (b : ℝ≥0∞)) ↔ a ≤ b := by
  rw [← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast, ENNReal.coe_le_coe]
  exact_mod_cast Iff.rfl

/-- The dyadic weight `2⁻¹ ^ σ.length` of one cylinder, as an exact nonnegative rational. -/
def BitString.weight (σ : BitString) : ℚ≥0 := 2⁻¹ ^ σ.length

theorem BitString.weight_pos (σ : BitString) : 0 < BitString.weight σ :=
  pow_pos (by norm_num) _

/-- Extending a string by one bit halves its dyadic weight. -/
theorem BitString.weight_append_singleton (σ : BitString) (b : Bool) :
    BitString.weight (σ ++ [b]) = 2⁻¹ * BitString.weight σ := by
  simp [BitString.weight, pow_succ, mul_comm]

/-- The total (un-normalized) weight of a finite cylinder family. -/
def totalWeight (F : Finset BitString) : ℚ≥0 := ∑ σ ∈ F, BitString.weight σ

theorem totalWeight_mono {F G : Finset BitString} (h : F ⊆ G) :
    totalWeight F ≤ totalWeight G :=
  Finset.sum_le_sum_of_subset h

section Examples
set_option linter.hashCommand false

#guard totalWeight {[false], [true]} = 1
#guard totalWeight {[true], [true, false]} = 3 / 4

end Examples

/-- The fair-coin measure of one cylinder is the cast of its exact weight. -/
theorem fairCoin_cylinder_eq_weight (σ : BitString) :
    fairCoin (cylinder σ) = (BitString.weight σ : ℝ≥0∞) := by
  rw [fairCoin_cylinder, BitString.weight, ← ENNReal.coe_nnratCast]
  push_cast
  rfl

/-! ## Exact measures of finite open sets -/

/-- The measure of a prefix-free family is the cast of its total weight. -/
theorem fairCoin_cylinderUnion_of_prefixFree {F : Finset BitString}
    (h : PrefixFree (F : Set BitString)) :
    fairCoin (cylinderUnion F) = (totalWeight F : ℝ≥0∞) := by
  rw [cylinderUnion, measure_biUnion_finset h.pairwiseDisjoint_cylinder
    fun σ _ ↦ measurableSet_cylinder σ, totalWeight, ← ENNReal.coe_nnratCast,
    NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl fun σ _ ↦ fairCoin_cylinder_eq_weight σ

/-- The exact measure of the finite open set named by `F`: the total weight of its prefix-free
normalization. This is the executable quantity that trimming constructions consume. -/
def finiteOpenWeight (F : Finset BitString) : ℚ≥0 := totalWeight (minimize F)

/-- The measure of an arbitrary finite cylinder family is the cast of its normalized weight. -/
theorem fairCoin_cylinderUnion (F : Finset BitString) :
    fairCoin (cylinderUnion F) = (finiteOpenWeight F : ℝ≥0∞) := by
  rw [← cylinderUnion_minimize, finiteOpenWeight,
    fairCoin_cylinderUnion_of_prefixFree (prefixFree_minimize F)]

section Examples
set_option linter.hashCommand false

#guard finiteOpenWeight {[true], [true, false]} = 1 / 2

end Examples

theorem finiteOpenWeight_mono {F G : Finset BitString} (h : F ⊆ G) :
    finiteOpenWeight F ≤ finiteOpenWeight G := by
  have hm := measure_mono (μ := fairCoin) (cylinderUnion_mono h)
  rw [fairCoin_cylinderUnion, fairCoin_cylinderUnion, ← ENNReal.coe_nnratCast,
    ← ENNReal.coe_nnratCast, ENNReal.coe_le_coe] at hm
  exact_mod_cast hm

theorem finiteOpenWeight_le_one (F : Finset BitString) : finiteOpenWeight F ≤ 1 := by
  have hm := prob_le_one (μ := fairCoin) (s := cylinderUnion F)
  rw [fairCoin_cylinderUnion, ← ENNReal.coe_nnratCast] at hm
  exact_mod_cast hm

/-! ## Countable prefix-free families

The measure of a union over an arbitrary prefix-free set of strings, which is what stopping-line
arguments need. Stated here beside the finite version rather than in any consumer. -/

/-- Generic cast reflection, `ℚ≥0` to `ℝ≥0∞`. -/
theorem coe_nnrat_le_coe {a b : ℚ≥0} : ((a : ℝ≥0∞) ≤ (b : ℝ≥0∞)) ↔ a ≤ b := by
  rw [← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast, ENNReal.coe_le_coe]
  exact_mod_cast Iff.rfl

/-- The measure of a union of cylinders over a prefix-free set of strings is the sum of their
weights. -/
theorem fairCoin_iUnion_cylinder_of_prefixFree {S : Set BitString} (hS : PrefixFree S) :
    fairCoin (⋃ σ ∈ S, cylinder σ) = ∑' σ : S, (BitString.weight σ.1 : ℝ≥0∞) := by
  rw [measure_biUnion S.to_countable hS.pairwiseDisjoint_cylinder
    fun σ _ ↦ measurableSet_cylinder σ]
  exact tsum_congr fun σ ↦ fairCoin_cylinder_eq_weight σ.1

/-- The finite Kraft inequality: a prefix-free family has total weight at most `1`. -/
theorem totalWeight_le_one_of_prefixFree {F : Finset BitString}
    (h : PrefixFree (F : Set BitString)) : totalWeight F ≤ 1 := by
  rw [show totalWeight F = finiteOpenWeight F by rw [finiteOpenWeight, minimize_eq_self_iff.mpr h]]
  exact finiteOpenWeight_le_one F

end AlgorithmicRandomness
