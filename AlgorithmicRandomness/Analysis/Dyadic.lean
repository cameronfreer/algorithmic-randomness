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
`1`; the endpoint values are *coherent* — refining an interval moves neither endpoint nor its
value, and the two children meet at a shared point with a shared value; and the chord slope
across `[σ]` is *exactly* the martingale's capital at `σ`.

Coherence is not yet the same as global well-definedness of a function on dyadic points. That
statement — equal dyadic points get equal values however they are named — additionally needs
uniqueness of the finite binary representation, and is left to the dense-extension step, where
working at a fixed level (on which `dyadicLeft` is injective, there being no trailing-zero
ambiguity) is the natural route.

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
  | b :: σ => (if b then 2⁻¹ else 0) + 2⁻¹ * dyadicLeft σ

/-- The width `2^-|σ|` of that interval. -/
noncomputable def dyadicWidth (σ : BitString) : ℝ := (2⁻¹ : ℝ) ^ σ.length

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

/-! ### Nesting

Extending a string shrinks its interval from both ends. These are the generic facts behind every
"the point stays inside every prefix interval" argument; they are stated for an arbitrary prefix
rather than for a single extra bit, since that is how they are always used. -/

theorem dyadicLeft_le_append (σ l : BitString) : dyadicLeft σ ≤ dyadicLeft (σ ++ l) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [← List.append_assoc, dyadicLeft_append]
    have hw := dyadicWidth_pos (σ ++ l)
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> linarith

theorem dyadicRight_append_le (σ l : BitString) : dyadicRight (σ ++ l) ≤ dyadicRight σ := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [← List.append_assoc, dyadicRight, dyadicLeft_append, dyadicWidth_append]
    rw [dyadicRight] at ih
    have hw := dyadicWidth_pos (σ ++ l)
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> linarith

theorem dyadicLeft_mono_of_prefix {σ τ : BitString} (h : σ <+: τ) :
    dyadicLeft σ ≤ dyadicLeft τ := by
  obtain ⟨l, rfl⟩ := h
  exact dyadicLeft_le_append σ l

theorem dyadicRight_anti_of_prefix {σ τ : BitString} (h : σ <+: τ) :
    dyadicRight τ ≤ dyadicRight σ := by
  obtain ⟨l, rfl⟩ := h
  exact dyadicRight_append_le σ l

theorem dyadicLeft_nonneg (σ : BitString) : 0 ≤ dyadicLeft σ := by
  simpa using dyadicLeft_mono_of_prefix (List.nil_prefix (l := σ))

theorem dyadicRight_le_one (σ : BitString) : dyadicRight σ ≤ 1 := by
  simpa using dyadicRight_anti_of_prefix (List.nil_prefix (l := σ))

theorem dyadicLeft_le_one (σ : BitString) : dyadicLeft σ ≤ 1 :=
  (dyadicLeft_lt_dyadicRight σ).le.trans (dyadicRight_le_one σ)

/-- Half-open cells, which partition. -/
def dyadicCell (σ : BitString) : Set ℝ := Set.Ico (dyadicLeft σ) (dyadicRight σ)

/-- Closed intervals, across which chords are taken. -/
def dyadicInterval (σ : BitString) : Set ℝ := Set.Icc (dyadicLeft σ) (dyadicRight σ)

theorem dyadicInterval_subset_of_prefix {σ τ : BitString} (h : σ <+: τ) :
    dyadicInterval τ ⊆ dyadicInterval σ :=
  Set.Icc_subset_Icc (dyadicLeft_mono_of_prefix h) (dyadicRight_anti_of_prefix h)

theorem dyadicInterval_subset_unit (σ : BitString) : dyadicInterval σ ⊆ Set.Icc (0 : ℝ) 1 := by
  simpa [dyadicInterval] using dyadicInterval_subset_of_prefix (List.nil_prefix (l := σ))

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

/-- **Cross-boundary coherence, endpoints**: the right end of the left child is the left end of
the right child. Together with the refinement lemmas this is what makes the endpoint value
depend only on the point, not on the string naming it. -/
theorem dyadicRight_append_false_eq_left_append_true (σ : BitString) :
    dyadicRight (σ ++ [false]) = dyadicLeft (σ ++ [true]) := by
  rw [dyadicRight, dyadicLeft_append, dyadicLeft_append, dyadicWidth_append]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring

/-- **Cross-boundary coherence, values**: and the cumulative function agrees there. -/
theorem cdfRight_append_false_eq_cdfLeft_append_true (M : TreeMartingale) (σ : BitString) :
    cdfRight M (σ ++ [false]) = cdfLeft M (σ ++ [true]) := by
  rw [cdfRight, cdfLeft_append, cdfLeft_append, if_pos rfl]
  simp only [Bool.false_eq_true, if_false]

/-- **The chord slope across `[σ]` is exactly the capital at `σ`.** -/
theorem cdf_slope (M : TreeMartingale) (σ : BitString) :
    (cdfRight M σ - cdfLeft M σ) / (dyadicRight σ - dyadicLeft σ)
      = ((M.capital σ : ℚ≥0) : ℝ) := by
  have hw : dyadicWidth σ ≠ 0 := (dyadicWidth_pos σ).ne'
  rw [cdfRight, dyadicRight, add_sub_cancel_left, add_sub_cancel_left, mul_comm,
    mul_div_assoc, div_self hw, mul_one]

end AlgorithmicRandomness
