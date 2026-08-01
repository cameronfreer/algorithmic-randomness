/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Martingale.Tree

/-!
# Ville's inequality

The combinatorial core is `sum_weight_capital_le`: the weighted capital of a finite prefix-free
family is bounded by the initial capital. Its proof compresses the deepest strings into their
parents, where the averaging law makes the two-child case an exact identity and the one-child
case a monotonicity step.

Ville's inequality then composes four facts: the stopping-line description of `reaches`, the
prefix-free measure theorem from the Cantor layer, the finite inequality above, and the passage
from finite subsums to a `tsum`.
-/

open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness
namespace TreeMartingale

variable (d : TreeMartingale)

/-- The two children of `τ` carry exactly the weighted capital of `τ`. -/
theorem sum_children (τ : BitString) :
    BitString.weight (τ ++ [false]) * d.capital (τ ++ [false])
      + BitString.weight (τ ++ [true]) * d.capital (τ ++ [true])
      = BitString.weight τ * d.capital τ := by
  rw [BitString.weight_append_singleton, BitString.weight_append_singleton, ← mul_add, d.fair τ,
    show 2⁻¹ * BitString.weight τ * (2 * d.capital τ)
      = (2⁻¹ * 2) * (BitString.weight τ * d.capital τ) by ring]
  norm_num

/-- Auxiliary induction: bound the weighted capital sum over a prefix-free family whose members
all have length at most `n`, by compressing the deepest strings into their parents. -/
theorem aux : ∀ (n : ℕ) (F : Finset BitString),
    PrefixFree (F : Set BitString) → (∀ σ ∈ F, σ.length ≤ n) →
    ∑ σ ∈ F, BitString.weight σ * d.capital σ ≤ d.capital [] := by
  intro n
  induction n with
  | zero =>
    intro F _ hlen
    have hsub : F ⊆ ({[]} : Finset BitString) := by
      intro σ hσ
      rw [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hlen σ hσ))
    calc ∑ σ ∈ F, BitString.weight σ * d.capital σ
        ≤ ∑ σ ∈ ({[]} : Finset BitString), BitString.weight σ * d.capital σ :=
          Finset.sum_le_sum_of_subset hsub
      _ = d.capital [] := by simp [BitString.weight]
  | succ n ih =>
    intro F hF hlen
    set F₁ := F.filter (fun σ ↦ σ.length ≤ n) with hF₁def
    set F₂ := F.filter (fun σ ↦ ¬ σ.length ≤ n) with hF₂def
    set I := F₂.image List.dropLast with hIdef
    have hlen₂ : ∀ σ ∈ F₂, σ.length = n + 1 := by
      intro σ hσ
      rw [hF₂def, Finset.mem_filter] at hσ
      have := hlen σ hσ.1
      omega
    have hmemF₂ : ∀ σ ∈ F₂, σ ∈ F := fun σ hσ ↦ (Finset.mem_filter.mp (hF₂def ▸ hσ)).1
    have hmemF₁ : ∀ σ ∈ F₁, σ ∈ F := fun σ hσ ↦ (Finset.mem_filter.mp (hF₁def ▸ hσ)).1
    have hlen₁ : ∀ σ ∈ F₁, σ.length ≤ n := by
      intro σ hσ
      rw [hF₁def, Finset.mem_filter] at hσ
      exact hσ.2
    have hlenG : ∀ σ ∈ F₁ ∪ I, σ.length ≤ n := by
      intro σ hσ
      rcases Finset.mem_union.mp hσ with h | h
      · exact hlen₁ σ h
      · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp (hIdef ▸ h)
        simp [hlen₂ ρ hρ]
    have hGF : ∀ σ ∈ F₁ ∪ I, ∃ ρ ∈ F, σ <+: ρ := by
      intro σ hσ
      rcases Finset.mem_union.mp hσ with h | h
      · exact ⟨σ, hmemF₁ σ h, List.prefix_refl σ⟩
      · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp (hIdef ▸ h)
        exact ⟨ρ, hmemF₂ ρ hρ, List.dropLast_prefix ρ⟩
    have hGpf : PrefixFree ((F₁ ∪ I : Finset BitString) : Set BitString) := by
      rw [prefixFree_iff]
      intro σ hσ τ hτ hpre
      rw [Finset.mem_coe] at hσ hτ
      rcases Finset.mem_union.mp hσ with h | h
      · obtain ⟨ρ, hρF, hτρ⟩ := hGF τ hτ
        have heq := (prefixFree_iff.mp hF) σ (hmemF₁ σ h) ρ hρF (hpre.trans hτρ)
        have hτσ : τ.length ≤ σ.length := by rw [heq]; exact hτρ.length_le
        exact hpre.eq_of_length (le_antisymm hpre.length_le hτσ)
      · obtain ⟨ρ, hρ, hρeq⟩ := Finset.mem_image.mp (hIdef ▸ h)
        have hlenσ : σ.length = n := by rw [← hρeq]; simp [hlen₂ ρ hρ]
        refine hpre.eq_of_length (le_antisymm hpre.length_le ?_)
        rw [hlenσ]
        exact hlenG τ hτ
    have hdisj : Disjoint F₁ I := by
      rw [Finset.disjoint_left]
      intro σ hσ₁ hσ₂
      obtain ⟨ρ, hρ, hρeq⟩ := Finset.mem_image.mp (hIdef ▸ hσ₂)
      have hpre : σ <+: ρ := by rw [← hρeq]; exact List.dropLast_prefix ρ
      have heq := (prefixFree_iff.mp hF) σ (hmemF₁ σ hσ₁) ρ (hmemF₂ ρ hρ) hpre
      have hl1 : σ.length ≤ n := hlen₁ σ hσ₁
      rw [heq, hlen₂ ρ hρ] at hl1
      omega
    have hfiber : ∑ τ ∈ I, ∑ σ ∈ F₂ with List.dropLast σ = τ,
        BitString.weight σ * d.capital σ = ∑ σ ∈ F₂, BitString.weight σ * d.capital σ :=
      Finset.sum_fiberwise_of_maps_to (fun σ hσ ↦ Finset.mem_image_of_mem _ hσ) _
    have hstep : ∀ τ ∈ I, ∑ σ ∈ F₂ with List.dropLast σ = τ,
        BitString.weight σ * d.capital σ ≤ BitString.weight τ * d.capital τ := by
      intro τ _
      have hsub : (F₂.filter fun σ ↦ List.dropLast σ = τ)
          ⊆ ({τ ++ [false], τ ++ [true]} : Finset BitString) := by
        intro σ hσ
        obtain ⟨hσ₂, hσd⟩ := Finset.mem_filter.mp hσ
        have hne : σ ≠ [] := fun h ↦ by simpa [h] using hlen₂ σ hσ₂
        have hcat : τ ++ [σ.getLast hne] = σ := by
          rw [← hσd]; exact List.dropLast_append_getLast hne
        cases hb : σ.getLast hne <;> rw [hb] at hcat <;> simp [← hcat]
      calc ∑ σ ∈ F₂ with List.dropLast σ = τ, BitString.weight σ * d.capital σ
          ≤ ∑ σ ∈ ({τ ++ [false], τ ++ [true]} : Finset BitString),
              BitString.weight σ * d.capital σ := Finset.sum_le_sum_of_subset hsub
        _ = BitString.weight τ * d.capital τ := by
            rw [Finset.sum_pair (by simp)]
            exact d.sum_children τ
    have h₂ : ∑ σ ∈ F₂, BitString.weight σ * d.capital σ
        ≤ ∑ τ ∈ I, BitString.weight τ * d.capital τ := by
      rw [← hfiber]
      exact Finset.sum_le_sum hstep
    have hFG : ∑ σ ∈ F, BitString.weight σ * d.capital σ
        ≤ ∑ σ ∈ F₁ ∪ I, BitString.weight σ * d.capital σ := by
      rw [Finset.sum_union hdisj, ← Finset.sum_filter_add_sum_filter_not F
        (fun σ ↦ σ.length ≤ n) fun σ ↦ BitString.weight σ * d.capital σ]
      exact add_le_add le_rfl h₂
    exact hFG.trans (ih (F₁ ∪ I) hGpf hlenG)

/-- The finite stopping-line inequality: the weighted capital of a prefix-free family is at
most the initial capital. -/
theorem sum_weight_capital_le {F : Finset BitString} (hF : PrefixFree (F : Set BitString)) :
    ∑ σ ∈ F, BitString.weight σ * d.capital σ ≤ d.capital [] :=
  d.aux (F.sup List.length) F hF fun _ hσ ↦ Finset.le_sup hσ

/-- On a prefix-free family whose capital everywhere reaches `q`, the total weight is bounded. -/
theorem mul_totalWeight_le {q : ℚ≥0} {F : Finset BitString}
    (hF : PrefixFree (F : Set BitString)) (hq : ∀ σ ∈ F, q ≤ d.capital σ) :
    q * totalWeight F ≤ d.capital [] := by
  rw [totalWeight, Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun σ hσ ↦ ?_) (d.sum_weight_capital_le hF)
  rw [mul_comm]
  gcongr
  exact hq σ hσ

/-! ## Ville's inequality -/

theorem fairCoin_reaches_eq_tsum_stopped (q : ℚ≥0) :
    fairCoin (d.reaches q) = ∑' σ : d.stopped q, (BitString.weight σ.1 : ℝ≥0∞) := by
  rw [d.reaches_eq_iUnion_stopped q,
    fairCoin_iUnion_cylinder_of_prefixFree (d.prefixFree_stopped q)]

/-- **Ville's inequality**: the measure of the set of points along which the capital reaches `q`
is at most the initial capital divided by `q`. -/
theorem fairCoin_reaches_le {q : ℚ≥0} (hq : 0 < q) :
    fairCoin (d.reaches q) ≤ (d.capital [] : ℝ≥0∞) / (q : ℝ≥0∞) := by
  rw [d.fairCoin_reaches_eq_tsum_stopped q, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  -- push the finite subfamily down to `BitString` and apply the finite inequality
  set F : Finset BitString := s.image Subtype.val with hFdef
  have hFmem : ∀ σ ∈ F, σ ∈ d.stopped q := by
    intro σ hσ
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp (hFdef ▸ hσ)
    exact τ.2
  have hsum : ∑ σ ∈ s, (BitString.weight σ.1 : ℝ≥0∞) = ∑ σ ∈ F, (BitString.weight σ : ℝ≥0∞) := by
    rw [hFdef, Finset.sum_image fun _ _ _ _ h ↦ Subtype.ext h]
  have hbound : q * totalWeight F ≤ d.capital [] :=
    d.mul_totalWeight_le (fun σ hσ τ hτ hne ↦
      (d.prefixFree_stopped q) (hFmem σ (by simpa using hσ)) (hFmem τ (by simpa using hτ)) hne)
      fun σ hσ ↦ (hFmem σ hσ).1
  have hcast : ∑ σ ∈ F, (BitString.weight σ : ℝ≥0∞) = ((totalWeight F : ℚ≥0) : ℝ≥0∞) := by
    rw [totalWeight, ← ENNReal.coe_nnratCast, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
    exact Finset.sum_congr rfl fun σ _ ↦ by rw [ENNReal.coe_nnratCast]
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.coe_nnratCast, ne_eq, ENNReal.coe_eq_zero]
    exact_mod_cast hq.ne'
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := by
    rw [← ENNReal.coe_nnratCast]; exact ENNReal.coe_ne_top
  rw [hsum, hcast, ENNReal.le_div_iff_mul_le (Or.inl hq0) (Or.inl hqtop),
    ← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  rw [mul_comm] at hbound
  exact_mod_cast hbound

end TreeMartingale
end AlgorithmicRandomness
