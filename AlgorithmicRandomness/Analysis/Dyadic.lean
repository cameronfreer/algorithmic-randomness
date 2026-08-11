/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Martingale.Tree

/-!
# Dyadic intervals and the cumulative endpoint function

A bit string `σ` names the dyadic interval `[0.σ, 0.σ + 2^-|σ|]`. This file gives the endpoints
and, for a tree martingale, the cumulative function at those endpoints — defined directly at
dyadic points rather than by first constructing a measure. The measure-theoretic object is a
separate concern and is deliberately not built here.

The acceptance checkpoint for this layer is threefold: the endpoint domain covers both `0` and
`1`; the values do not depend on which finite binary representation of a dyadic point is used;
and the chord slope across `[σ]` is *exactly* the martingale's capital at `σ`.

Half-open cells are what partition, and closed intervals are what chords are taken across; both
are provided, since the two roles are genuinely different and conflating them fails at points
whose binary expansion is eventually constant.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-! ## Endpoints -/

/-- The left endpoint `0.σ` of the dyadic interval named by `σ`. -/
noncomputable def dyadicLeft : BitString → ℝ
  | [] => 0
  | b :: σ => (if b then 1 / 2 else 0) + (1 / 2) * dyadicLeft σ

/-- The width `2^-|σ|` of that interval. -/
noncomputable def dyadicWidth (σ : BitString) : ℝ := (1 / 2) ^ σ.length

/-- The right endpoint `0.σ + 2^-|σ|`. -/
noncomputable def dyadicRight (σ : BitString) : ℝ := dyadicLeft σ + dyadicWidth σ

@[simp] theorem dyadicLeft_nil : dyadicLeft [] = 0 := rfl
@[simp] theorem dyadicWidth_nil : dyadicWidth [] = 1 := by rw [dyadicWidth]; norm_num
@[simp] theorem dyadicRight_nil : dyadicRight [] = 1 := by rw [dyadicRight]; norm_num

theorem dyadicWidth_pos (σ : BitString) : 0 < dyadicWidth σ := by
  rw [dyadicWidth]; positivity

theorem dyadicWidth_append (σ : BitString) (b : Bool) :
    dyadicWidth (σ ++ [b]) = dyadicWidth σ / 2 := by
  rw [dyadicWidth, dyadicWidth, List.length_append, List.length_singleton, pow_succ]
  ring

/-- Extending on the right moves the left endpoint by the new bit's weight. -/
theorem dyadicWidth_cons (c : Bool) (σ : BitString) :
    dyadicWidth (c :: σ) = dyadicWidth σ / 2 := by
  rw [dyadicWidth, dyadicWidth, List.length_cons, pow_succ]
  ring

theorem dyadicLeft_append (σ : BitString) (b : Bool) :
    dyadicLeft (σ ++ [b]) = dyadicLeft σ + (if b then dyadicWidth σ / 2 else 0) := by
  induction σ with
  | nil => cases b <;> simp [dyadicLeft, dyadicWidth]
  | cons c σ ih =>
    rw [List.cons_append, dyadicLeft, ih, dyadicLeft, dyadicWidth_cons]
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

/-- The two children split the parent interval at its midpoint. -/
theorem dyadicLeft_append_false (σ : BitString) : dyadicLeft (σ ++ [false]) = dyadicLeft σ := by
  rw [dyadicLeft_append]; simp

theorem dyadicRight_append_true (σ : BitString) : dyadicRight (σ ++ [true]) = dyadicRight σ := by
  rw [dyadicRight, dyadicRight, dyadicLeft_append, dyadicWidth_append]
  simp only [reduceIte]
  ring

theorem dyadicLeft_lt_dyadicRight (σ : BitString) : dyadicLeft σ < dyadicRight σ := by
  rw [dyadicRight]
  linarith [dyadicWidth_pos σ]

/-- Half-open cells, which partition. -/
def dyadicCell (σ : BitString) : Set ℝ := Set.Ico (dyadicLeft σ) (dyadicRight σ)

/-- Closed intervals, across which chords are taken. -/
def dyadicInterval (σ : BitString) : Set ℝ := Set.Icc (dyadicLeft σ) (dyadicRight σ)

/-! ## The cumulative endpoint function -/

/-- One step: moving into the right child skips the left child's mass. -/
noncomputable def cdfStep (M : TreeMartingale) (q : BitString × ℝ) (b : Bool) : BitString × ℝ :=
  (q.1 ++ [b],
    if b then q.2 + dyadicWidth (q.1 ++ [false]) * ((M.capital (q.1 ++ [false]) : ℚ≥0) : ℝ)
    else q.2)

noncomputable def cdfPair (M : TreeMartingale) (σ : BitString) : BitString × ℝ :=
  σ.foldl (cdfStep M) ([], 0)

/-- The cumulative function at the left endpoint of `[σ]`. -/
noncomputable def cdfLeft (M : TreeMartingale) (σ : BitString) : ℝ := (cdfPair M σ).2

/-- The cumulative function at the right endpoint of `[σ]`. -/
noncomputable def cdfRight (M : TreeMartingale) (σ : BitString) : ℝ :=
  cdfLeft M σ + dyadicWidth σ * ((M.capital σ : ℚ≥0) : ℝ)

theorem foldl_cdfStep_fst (M : TreeMartingale) (σ : BitString) :
    ∀ (τ : BitString) (v : ℝ), (σ.foldl (cdfStep M) (τ, v)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ v; simp
  | cons b σ ih => intro τ v; rw [List.foldl_cons, ih]; simp [cdfStep]

@[simp] theorem cdfPair_fst (M : TreeMartingale) (σ : BitString) : (cdfPair M σ).1 = σ := by
  rw [cdfPair, foldl_cdfStep_fst, List.nil_append]

theorem cdfLeft_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    cdfLeft M (σ ++ [b])
      = if b then cdfLeft M σ + dyadicWidth (σ ++ [false]) * ((M.capital (σ ++ [false]) : ℚ≥0) : ℝ)
        else cdfLeft M σ := by
  have h : cdfPair M (σ ++ [b]) = cdfStep M (cdfPair M σ) b := by
    rw [cdfPair, cdfPair, List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold cdfLeft
  rw [h, cdfStep, cdfPair_fst]

/-! ## The acceptance checkpoint -/

@[simp] theorem cdfLeft_nil (M : TreeMartingale) : cdfLeft M [] = 0 := rfl

/-- The endpoint domain covers `0`. -/
theorem cdfLeft_at_zero (M : TreeMartingale) : dyadicLeft ([] : BitString) = 0 ∧
    cdfLeft M [] = 0 := ⟨dyadicLeft_nil, cdfLeft_nil M⟩

/-- The endpoint domain covers `1`, where the value is the total mass. -/
theorem cdfRight_at_one (M : TreeMartingale) : dyadicRight ([] : BitString) = 1 ∧
    cdfRight M [] = ((M.capital [] : ℚ≥0) : ℝ) := by
  refine ⟨dyadicRight_nil, ?_⟩
  rw [cdfRight, cdfLeft_nil, dyadicWidth_nil]
  ring

/-- **Representation independence, left**: appending `false` does not move the left endpoint,
and does not change the value there. -/
theorem cdfLeft_append_false (M : TreeMartingale) (σ : BitString) :
    cdfLeft M (σ ++ [false]) = cdfLeft M σ := by
  rw [cdfLeft_append]; simp

/-- **Representation independence, right**: appending `true` does not move the right endpoint,
and does not change the value there. This is where fairness is used. -/
theorem cdfRight_append_true (M : TreeMartingale) (σ : BitString) :
    cdfRight M (σ ++ [true]) = cdfRight M σ := by
  have hfair : ((M.capital (σ ++ [false]) : ℚ≥0) : ℝ) + ((M.capital (σ ++ [true]) : ℚ≥0) : ℝ)
      = 2 * ((M.capital σ : ℚ≥0) : ℝ) := by exact_mod_cast M.fair σ
  rw [cdfRight, cdfRight, cdfLeft_append, if_pos rfl, dyadicWidth_append, dyadicWidth_append]
  linear_combination (dyadicWidth σ / 2) * hfair

/-- **The chord slope across `[σ]` is exactly the capital at `σ`.** -/
theorem cdf_slope (M : TreeMartingale) (σ : BitString) :
    (cdfRight M σ - cdfLeft M σ) / (dyadicRight σ - dyadicLeft σ)
      = ((M.capital σ : ℚ≥0) : ℝ) := by
  have hw : dyadicWidth σ ≠ 0 := (dyadicWidth_pos σ).ne'
  rw [cdfRight, dyadicRight, add_sub_cancel_left, add_sub_cancel_left, mul_comm,
    mul_div_assoc, div_self hw, mul_one]

end AlgorithmicRandomness
