/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Martingale.Computable

/-!
# The savings property

A martingale has the *savings property* when its capital never falls more than `1` below any
earlier value. Stated without subtraction, since `ℚ≥0` subtraction truncates:

  `M σ ≤ M (σ ++ τ) + 1`.

Every martingale can be normalized to one with this property that still succeeds on exactly the
same points, and the normalization is uniform in the martingale: it does not look at any path.

## The construction

Split the capital into a **savings** account `s` and an **active** account `a`, with total
`s + a` and the invariant `a ≤ 1`. The active account bets in proportion to the source
martingale; when it would exceed `1`, half of it is banked:

  `a' := a * M (σ ++ [b]) / M σ`,  then  `(s, a) ↦ if 1 < a' then (s + a'/2, a'/2) else (s, a')`.

Three things make this work, and they are independent of one another.

* **Fairness** holds because the total is `s + a'` in *both* branches, so the two children sum
  to `2 (s + a)` whatever the branch taken.
* **The invariant** `a ≤ 1` holds because `a' ≤ 2` — the source is a martingale, so a child's
  capital is at most twice its parent's — hence `a'/2 ≤ 1` after banking.
* **The savings property** follows at once: the total is at most `s + 1`, savings never
  decrease, and the total is always at least the savings.

Banking *half* rather than a fixed amount is what keeps the construction free of subtraction.
Each banking event still adds more than `1/2`, which is what drives success: if banking ever
stopped along a path, the active account would track the source martingale upward against the
bound `a ≤ 1`.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-! ## The positive shift

Betting in proportion requires a positive denominator, so the source is shifted first. -/

/-- Add `1` to every value. Preserves fairness and success, and makes the capital positive. -/
def TreeMartingale.shift (M : TreeMartingale) : TreeMartingale where
  capital σ := M.capital σ + 1
  fair σ := by
    have h : M.capital (σ ++ [false]) + 1 + (M.capital (σ ++ [true]) + 1)
        = (M.capital (σ ++ [false]) + M.capital (σ ++ [true])) + 2 := by ring
    rw [h, M.fair σ]
    ring

@[simp] theorem TreeMartingale.shift_capital (M : TreeMartingale) (σ : BitString) :
    M.shift.capital σ = M.capital σ + 1 := rfl

theorem TreeMartingale.shift_pos (M : TreeMartingale) (σ : BitString) :
    0 < M.shift.capital σ := by
  rw [shift_capital]
  positivity

theorem TreeMartingale.succeeds_shift {M : TreeMartingale} {x : Cantor} (h : M.Succeeds x) :
    M.shift.Succeeds x := by
  intro c
  obtain ⟨n, hn⟩ := h c
  exact ⟨n, by rw [shift_capital]; exact le_add_right hn⟩

/-- A child's capital is at most twice its parent's. -/
theorem TreeMartingale.capital_append_le_two_mul (M : TreeMartingale) (σ : BitString) (b : Bool) :
    M.capital (σ ++ [b]) ≤ 2 * M.capital σ := M.capital_le_two_mul σ b

/-! ## The two-account fold -/

/-- The betting factor of `M` at `σ` on bit `b`. -/
def bettingFactor (M : TreeMartingale) (σ : BitString) (b : Bool) : ℚ≥0 :=
  M.capital (σ ++ [b]) / M.capital σ

theorem bettingFactor_add (M : TreeMartingale) (σ : BitString) (hσ : 0 < M.capital σ) :
    bettingFactor M σ false + bettingFactor M σ true = 2 := by
  rw [bettingFactor, bettingFactor, ← add_div, M.fair σ]
  field_simp

theorem bettingFactor_le_two (M : TreeMartingale) (σ : BitString) (b : Bool)
    (hσ : 0 < M.capital σ) : bettingFactor M σ b ≤ 2 := by
  rw [bettingFactor, div_le_iff₀ hσ]
  simpa [mul_comm] using M.capital_append_le_two_mul σ b

/-- One step of the fold: bet the active account in proportion, banking half when it would
exceed `1`. -/
def savingsStep (M : TreeMartingale) (q : BitString × ℚ≥0 × ℚ≥0) (b : Bool) :
    BitString × ℚ≥0 × ℚ≥0 :=
  let a' := q.2.2 * bettingFactor M q.1 b
  (q.1 ++ [b], if 1 < a' then (q.2.1 + a' / 2, a' / 2) else (q.2.1, a'))

/-- Walk to `σ`, carrying the prefix and the two accounts. -/
def savingsPair (M : TreeMartingale) (σ : BitString) : BitString × ℚ≥0 × ℚ≥0 :=
  σ.foldl (savingsStep M) ([], (0, 1 / 2))

/-- The savings account at `σ`. -/
def savingsPart (M : TreeMartingale) (σ : BitString) : ℚ≥0 := (savingsPair M σ).2.1

/-- The active account at `σ`. -/
def activePart (M : TreeMartingale) (σ : BitString) : ℚ≥0 := (savingsPair M σ).2.2

/-- The normalized capital: savings plus active. -/
def savingsCapital (M : TreeMartingale) (σ : BitString) : ℚ≥0 :=
  savingsPart M σ + activePart M σ

theorem foldl_savingsStep_fst (M : TreeMartingale) (σ : BitString) :
    ∀ (τ : BitString) (p : ℚ≥0 × ℚ≥0), (σ.foldl (savingsStep M) (τ, p)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ p; simp
  | cons b σ ih => intro τ p; rw [List.foldl_cons, ih]; simp [savingsStep]

@[simp] theorem savingsPair_fst (M : TreeMartingale) (σ : BitString) :
    (savingsPair M σ).1 = σ := by
  rw [savingsPair, foldl_savingsStep_fst, List.nil_append]

theorem savingsPair_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    savingsPair M (σ ++ [b]) = savingsStep M (savingsPair M σ) b := by
  rw [savingsPair, savingsPair, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem savingsPart_nil (M : TreeMartingale) : savingsPart M [] = 0 := rfl
@[simp] theorem activePart_nil (M : TreeMartingale) : activePart M [] = 1 / 2 := rfl

/-- The active account after one step, before the banking decision. -/
def nextActive (M : TreeMartingale) (σ : BitString) (b : Bool) : ℚ≥0 :=
  activePart M σ * bettingFactor M σ b

theorem savings_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    savingsPart M (σ ++ [b])
      = if 1 < nextActive M σ b then savingsPart M σ + nextActive M σ b / 2
        else savingsPart M σ := by
  have h : savingsPair M (σ ++ [b]) = savingsStep M (savingsPair M σ) b :=
    savingsPair_append M σ b
  unfold nextActive savingsPart activePart
  rw [h, savingsStep, savingsPair_fst]
  by_cases hc : 1 < (savingsPair M σ).2.2 * bettingFactor M σ b
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

theorem active_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    activePart M (σ ++ [b])
      = if 1 < nextActive M σ b then nextActive M σ b / 2 else nextActive M σ b := by
  have h : savingsPair M (σ ++ [b]) = savingsStep M (savingsPair M σ) b :=
    savingsPair_append M σ b
  unfold nextActive activePart
  rw [h, savingsStep, savingsPair_fst]
  by_cases hc : 1 < (savingsPair M σ).2.2 * bettingFactor M σ b
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

/-- **The total is the natural one on both branches**, which is what makes fairness exact. -/
theorem savingsCapital_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    savingsCapital M (σ ++ [b]) = savingsPart M σ + nextActive M σ b := by
  rw [savingsCapital, savings_append, active_append]
  split
  · rw [add_assoc, ← add_div]
    congr 1
    rw [← two_mul, mul_comm, mul_div_assoc, div_self (two_ne_zero), mul_one]
  · rfl

/-! ## The invariants -/

variable {M : TreeMartingale}

/-- Savings never decrease in one step. -/
theorem savingsPart_le_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    savingsPart M σ ≤ savingsPart M (σ ++ [b]) := by
  rw [savings_append]
  split
  · exact le_add_right (le_refl _)
  · exact le_refl _

/-- Savings never decrease along any extension. -/
theorem savingsPart_mono (M : TreeMartingale) (σ τ : BitString) :
    savingsPart M σ ≤ savingsPart M (σ ++ τ) := by
  induction τ using List.reverseRecOn with
  | nil => simp
  | append_singleton τ b ih =>
    rw [← List.append_assoc]
    exact ih.trans (savingsPart_le_append M (σ ++ τ) b)

/-- The active account never exceeds `1`: the banking rule halves anything above it, and a
child's betting factor is at most `2`. -/
theorem activePart_le_one (hpos : ∀ σ, 0 < M.capital σ) (σ : BitString) :
    activePart M σ ≤ 1 := by
  induction σ using List.reverseRecOn with
  | nil => rw [activePart_nil]; norm_num
  | append_singleton σ b ih =>
    rw [active_append]
    split
    · -- banked: the natural value is at most `2`, so half of it is at most `1`
      rw [div_le_one (by norm_num)]
      rw [nextActive]
      calc activePart M σ * bettingFactor M σ b
          ≤ 1 * 2 := mul_le_mul' ih (bettingFactor_le_two M σ b (hpos σ))
        _ = 2 := one_mul 2
    · exact not_lt.mp ‹¬ 1 < nextActive M σ b›

theorem savingsCapital_le (hpos : ∀ σ, 0 < M.capital σ) (σ : BitString) :
    savingsCapital M σ ≤ savingsPart M σ + 1 := by
  rw [savingsCapital]
  gcongr
  exact activePart_le_one hpos σ

theorem savingsPart_le_savingsCapital (M : TreeMartingale) (σ : BitString) :
    savingsPart M σ ≤ savingsCapital M σ := le_add_right (le_refl _)

/-! ## Fairness and the savings property -/

/-- The normalized capital is a martingale. Fairness is exact because the total after one step
is the natural total on *both* branches. -/
theorem savingsCapital_fair (hpos : ∀ σ, 0 < M.capital σ) (σ : BitString) :
    savingsCapital M (σ ++ [false]) + savingsCapital M (σ ++ [true])
      = 2 * savingsCapital M σ := by
  rw [savingsCapital_append, savingsCapital_append, nextActive, nextActive]
  rw [show savingsPart M σ + activePart M σ * bettingFactor M σ false
        + (savingsPart M σ + activePart M σ * bettingFactor M σ true)
      = 2 * savingsPart M σ
        + activePart M σ * (bettingFactor M σ false + bettingFactor M σ true) by ring,
    bettingFactor_add M σ (hpos σ), savingsCapital]
  ring

/-- **The savings property**: the capital never falls more than `1` below an earlier value. -/
theorem savingsCapital_savings (hpos : ∀ σ, 0 < M.capital σ) (σ τ : BitString) :
    savingsCapital M σ ≤ savingsCapital M (σ ++ τ) + 1 := by
  calc savingsCapital M σ
      ≤ savingsPart M σ + 1 := savingsCapital_le hpos σ
    _ ≤ savingsPart M (σ ++ τ) + 1 := by gcongr; exact savingsPart_mono M σ τ
    _ ≤ savingsCapital M (σ ++ τ) + 1 := by
        gcongr; exact savingsPart_le_savingsCapital M (σ ++ τ)

end AlgorithmicRandomness
