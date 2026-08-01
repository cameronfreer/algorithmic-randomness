/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.NNRatCode
import AlgorithmicRandomness.EffectiveOpen.Trim
import AlgorithmicRandomness.Randomness.Schnorr

/-!
# Exact finite-stage approximation for Schnorr tests

Gate 1 of the bridge from Schnorr randomness to computable randomness. The conditional
probability `μ (Uₙ ∩ [σ])` is only a computable real, but each *finite stage* of `Uₙ` meets
`[σ]` in a finite union of cylinders whose measure is an exact rational, and the Schnorr
modulus bounds the error.

Two representations again, for the reason established in the trimming file: `capWeight` is the
semantic `ℚ≥0`-valued measure of `cylinderUnion F ∩ cylinder σ`, while `capWeightCode` is the
executable `ℕ`-valued version on `List BitString` that a program can actually run — mathlib has
no `Primcodable (Finset α)` and no `Primcodable ℚ≥0`, so the approximation program must go
through the list-valued stage representation.

The two error bounds are stated *additively* rather than with a difference, to avoid `ℝ≥0∞`
subtraction and to convert cleanly into a real absolute-error estimate later.
-/

open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## Meeting a cylinder -/

/-- The string naming `cylinder τ ∩ cylinder σ`, or `none` when the cylinders are disjoint. -/
def meet (τ σ : BitString) : Option BitString :=
  if prefixB τ σ then some σ else if prefixB σ τ then some τ else none

theorem cylinder_inter_cylinder (τ σ : BitString) :
    cylinder τ ∩ cylinder σ = (meet τ σ).elim ∅ cylinder := by
  unfold meet
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
def meetList (L : List BitString) (σ : BitString) : List BitString :=
  L.filterMap fun τ ↦ meet τ σ

theorem cylinderUnion_inter_cylinder (L : List BitString) (σ : BitString) :
    cylinderUnion L.toFinset ∩ cylinder σ = cylinderUnion (meetList L σ).toFinset := by
  ext x
  simp only [Set.mem_inter_iff, mem_cylinderUnion, List.mem_toFinset, meetList,
    List.mem_filterMap]
  constructor
  · rintro ⟨⟨τ, hτ, hxτ⟩, hxσ⟩
    have hmem : x ∈ cylinder τ ∩ cylinder σ := ⟨hxτ, hxσ⟩
    rw [cylinder_inter_cylinder] at hmem
    cases hm : meet τ σ with
    | none => rw [hm] at hmem; exact absurd hmem (Set.notMem_empty x)
    | some ρ => exact ⟨ρ, ⟨τ, hτ, hm⟩, by rw [hm] at hmem; exact hmem⟩
  · rintro ⟨ρ, ⟨τ, hτ, hm⟩, hxρ⟩
    have : x ∈ cylinder τ ∩ cylinder σ := by
      rw [cylinder_inter_cylinder, hm]; exact hxρ
    exact ⟨⟨τ, hτ, this.1⟩, this.2⟩

/-! ## The exact rational measure -/

/-- The exact measure of `cylinderUnion F ∩ cylinder σ`, semantically. -/
noncomputable def capWeight (F : Finset BitString) (σ : BitString) : ℚ≥0 :=
  finiteOpenWeight (meetList F.toList σ).toFinset

theorem meetList_toFinset_congr {L L' : List BitString} (h : ∀ τ, τ ∈ L ↔ τ ∈ L')
    (σ : BitString) : (meetList L σ).toFinset = (meetList L' σ).toFinset := by
  ext ρ
  simp only [List.mem_toFinset, meetList, List.mem_filterMap]
  exact ⟨fun ⟨τ, hτ, hm⟩ ↦ ⟨τ, (h τ).mp hτ, hm⟩, fun ⟨τ, hτ, hm⟩ ↦ ⟨τ, (h τ).mpr hτ, hm⟩⟩

theorem capWeight_toFinset (L : List BitString) (σ : BitString) :
    capWeight L.toFinset σ = finiteOpenWeight (meetList L σ).toFinset := by
  rw [capWeight, meetList_toFinset_congr (L := L.toFinset.toList) (L' := L) (fun τ ↦ by simp) σ]

theorem fairCoin_cylinderUnion_inter_cylinder (L : List BitString) (σ : BitString) :
    fairCoin (cylinderUnion L.toFinset ∩ cylinder σ) = (capWeight L.toFinset σ : ℝ≥0∞) := by
  rw [cylinderUnion_inter_cylinder, fairCoin_cylinderUnion, capWeight_toFinset]

/-! ## The executable version -/

/-- The coded exact measure of `cylinderUnion L.toFinset ∩ cylinder σ`, computed entirely in
`ℕ`: numerator `natWeight`, denominator the matching power of two. -/
def capWeightCode (L : List BitString) (σ : BitString) : ℕ :=
  Nat.pair (natWeight (maxLen (meetList L σ)) (meetList L σ)) (2 ^ maxLen (meetList L σ) - 1)

theorem value_capWeightCode (L : List BitString) (σ : BitString) :
    NNRatCode.value (capWeightCode L σ) = capWeight L.toFinset σ := by
  rw [capWeightCode, NNRatCode.value_pair, Nat.sub_add_cancel Nat.one_le_two_pow,
    capWeight_toFinset, natWeight_cast]
  push_cast
  rw [mul_comm, mul_div_assoc,
    div_self (by positivity : ((2 : ℚ≥0) ^ maxLen (meetList L σ)) ≠ 0), mul_one]

theorem primrec_meet : Primrec₂ meet := by
  unfold meet
  refine Primrec.ite (Primrec.eq.comp primrec_prefixB (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) ?_
  exact Primrec.ite
    (Primrec.eq.comp (primrec_prefixB.comp Primrec.snd Primrec.fst) (Primrec.const true))
    (Primrec.option_some.comp Primrec.fst) (Primrec.const none)

theorem primrec_meetList : Primrec₂ meetList :=
  Primrec.listFilterMap Primrec.fst (primrec_meet.comp Primrec.snd (Primrec.snd.comp Primrec.fst))

theorem primrec_capWeightCode : Primrec₂ capWeightCode := by
  have hm : Primrec fun z : List BitString × BitString ↦ meetList z.1 z.2 := primrec_meetList
  have hlen : Primrec fun z : List BitString × BitString ↦ maxLen (meetList z.1 z.2) :=
    primrec_maxLen.comp hm
  refine Primrec₂.natPair.comp (primrec_natWeight.comp hlen hm) ?_
  exact Primrec.nat_sub.comp
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) hlen) (Primrec.const 1)

/-! ## The two error bounds

Both are stated additively, so that no `ℝ≥0∞` subtraction ever appears. -/

/-- Stage error: at the modulus stage, the unenumerated part of `Uₙ` contributes at most `2⁻ᵏ`,
uniformly over the conditioning cylinder. -/
theorem stage_error (T : SchnorrTest) (n k : ℕ) (σ : BitString) :
    fairCoin (T.openCode.denote n ∩ cylinder σ)
      ≤ fairCoin (T.openCode.stageSet n (T.modulus.apply₂ n k) ∩ cylinder σ)
        + (2⁻¹ : ℝ≥0∞) ^ k := by
  have hsub : T.openCode.denote n ∩ cylinder σ
      ⊆ (T.openCode.stageSet n (T.modulus.apply₂ n k) ∩ cylinder σ)
        ∪ (T.openCode.denote n \ T.openCode.stageSet n (T.modulus.apply₂ n k)) := by
    rintro x ⟨hx, hxσ⟩
    by_cases hs : x ∈ T.openCode.stageSet n (T.modulus.apply₂ n k)
    · exact Or.inl ⟨hs, hxσ⟩
    · exact Or.inr ⟨hx, hs⟩
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  gcongr
  exact T.tail_le n k

/-- Truncation error: the level bounds sum geometrically past any cutoff. -/
theorem tail_error (T : SchnorrTest) (N : ℕ) (σ : BitString) :
    ∑' n : ℕ, fairCoin (T.openCode.denote (N + n) ∩ cylinder σ) ≤ (2⁻¹ : ℝ≥0∞) ^ N * 2 := by
  have hterm : ∀ n : ℕ, fairCoin (T.openCode.denote (N + n) ∩ cylinder σ)
      ≤ (2⁻¹ : ℝ≥0∞) ^ N * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    refine le_trans (measure_mono Set.inter_subset_left) ?_
    rw [← pow_add]
    exact T.measure_le (N + n)
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

end AlgorithmicRandomness
