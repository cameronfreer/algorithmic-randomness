/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.FiniteOpen

/-!
# Tree martingales

A `TreeMartingale` is a betting strategy on the full binary tree: a nonnegative rational
capital function satisfying the exact averaging law. The name keeps it clearly distinct from
`MeasureTheory.Martingale`, to which it will later be bridged.

This file provides the semantics — the averaging law and its consequences, the set of points
along which the capital reaches a threshold, and the stopping line of prefix-minimal strings at
which that first happens. Ville's inequality is in `Martingale.Ville`.
-/

open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-- A nonnegative rational tree martingale: the exact averaging law on the binary tree. -/
structure TreeMartingale where
  /-- The capital held after betting along `σ`. -/
  capital : BitString → ℚ≥0
  /-- Fairness: the two children average to the parent. -/
  fair : ∀ σ, capital (σ ++ [false]) + capital (σ ++ [true]) = 2 * capital σ

namespace TreeMartingale

variable (d : TreeMartingale)

/-- A child's capital is at most twice its parent's: the sibling's capital is nonnegative by
the type of `capital`. -/
theorem capital_le_two_mul (σ : BitString) (b : Bool) :
    d.capital (σ ++ [b]) ≤ 2 * d.capital σ := by
  rw [← d.fair σ]
  cases b
  · exact le_add_right (le_refl _)
  · exact le_add_left (le_refl _)

/-! ## Reaching a threshold -/

/-- The points along which the capital reaches `q`. -/
def reaches (q : ℚ≥0) : Set Cantor := {x | ∃ n, q ≤ d.capital (initSeg x n)}

variable {d}

theorem mem_reaches_iff {q : ℚ≥0} {x : Cantor} :
    x ∈ d.reaches q ↔ ∃ σ, q ≤ d.capital σ ∧ x ∈ cylinder σ := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨initSeg x n, hn, mem_cylinder_initSeg x n⟩
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ.length, by rwa [initSeg_of_mem_cylinder hx]⟩

variable (d)

theorem reaches_eq_iUnion (q : ℚ≥0) :
    d.reaches q = ⋃ σ ∈ {σ : BitString | q ≤ d.capital σ}, cylinder σ := by
  ext x
  rw [mem_reaches_iff, Set.mem_iUnion₂]
  exact ⟨fun ⟨σ, h1, h2⟩ ↦ ⟨σ, h1, h2⟩, fun ⟨σ, h1, h2⟩ ↦ ⟨σ, h1, h2⟩⟩

theorem isOpen_reaches (q : ℚ≥0) : IsOpen (d.reaches q) := by
  rw [reaches_eq_iUnion]
  exact isOpen_biUnion fun σ _ ↦ (isClopen_cylinder σ).isOpen

theorem measurableSet_reaches (q : ℚ≥0) : MeasurableSet (d.reaches q) :=
  (d.isOpen_reaches q).measurableSet

/-! ## The stopping line -/

/-- The prefix-minimal strings at which the capital first reaches `q`. -/
def stopped (q : ℚ≥0) : Set BitString :=
  {σ | q ≤ d.capital σ ∧ ∀ τ, τ <+: σ → τ ≠ σ → ¬q ≤ d.capital τ}

theorem le_capital_of_mem_stopped {q : ℚ≥0} {σ : BitString} (h : σ ∈ d.stopped q) :
    q ≤ d.capital σ := h.1

/-- The stopping line is prefix-free: a proper prefix of a stopped string is not stopped. -/
theorem prefixFree_stopped (q : ℚ≥0) : PrefixFree (d.stopped q) := by
  rw [prefixFree_iff]
  intro σ hσ τ hτ hpre
  by_contra hne
  exact hτ.2 σ hpre hne hσ.1

/-- Every point that reaches `q` does so first at a unique stopped string. -/
theorem reaches_eq_iUnion_stopped (q : ℚ≥0) :
    d.reaches q = ⋃ σ ∈ d.stopped q, cylinder σ := by
  ext x
  rw [mem_reaches_iff, Set.mem_iUnion₂]
  refine ⟨fun ⟨σ, hσ, hx⟩ ↦ ?_, fun ⟨σ, hσ, hx⟩ ↦ ⟨σ, hσ.1, hx⟩⟩
  -- pass to the shortest prefix of `x` whose capital already reaches `q`
  classical
  have hex : ∃ n, q ≤ d.capital (initSeg x n) :=
    ⟨σ.length, by rwa [initSeg_of_mem_cylinder hx]⟩
  refine ⟨initSeg x (Nat.find hex), ⟨Nat.find_spec hex, fun τ hpre hne hτ ↦ ?_⟩,
    mem_cylinder_initSeg x _⟩
  have hlen : τ.length < Nat.find hex := by
    have h1 : τ.length ≤ (initSeg x (Nat.find hex)).length := hpre.length_le
    rw [length_initSeg] at h1
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd (hpre.eq_of_length (by rw [h, length_initSeg])) hne
  have heq : initSeg x τ.length = τ :=
    initSeg_of_mem_cylinder (cylinder_anti hpre (mem_cylinder_initSeg x _))
  exact Nat.find_min hex hlen (by rw [heq]; exact hτ)

end TreeMartingale

end AlgorithmicRandomness
