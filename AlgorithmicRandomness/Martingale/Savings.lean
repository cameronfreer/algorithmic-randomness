/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.Partrec
import AlgorithmicRandomness.Coding.TotalCode
import AlgorithmicRandomness.Martingale.Computable

/-!
# The savings property

A martingale has the *savings property* when its capital never falls more than `1` below any
earlier value. Stated without subtraction, since `ℚ≥0` subtraction truncates:

  `M σ ≤ M (σ ++ τ) + 1`.

Every martingale can be normalized to one with this property that still succeeds wherever the
source succeeds, and the normalization is uniform in the martingale: it does not look at any
path. (Only that direction is proved here; it is the one the oscillator needs.)

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

/-- The capital never falls more than `1` below any earlier value. Stated without subtraction,
since `ℚ≥0` subtraction truncates. -/
def TreeMartingale.SavingsProperty (M : TreeMartingale) : Prop :=
  ∀ σ τ, M.capital σ ≤ M.capital (σ ++ τ) + 1

/-! ## Linear growth, and convergence along a successful path

The savings property bounds how far the capital can fall; combined with fairness it also bounds how
fast it can *rise*, since a child's gain is the sibling's loss and the sibling cannot lose more than
`1`. The linear bound is what makes the mass of a level-`n` cell tend to zero, and the convergence
theorem replaces "unbounded" by "tends to infinity" without any reference to the banked account. -/

/-- One step. Savings applied to the *sibling*, together with fairness, bounds a child's gain. -/
private theorem capital_append_le_add_one {M : TreeMartingale} (hs : M.SavingsProperty)
    (σ : BitString) (b : Bool) : M.capital (σ ++ [b]) ≤ M.capital σ + 1 := by
  have hfair := M.fair σ
  refine (add_le_add_iff_right (M.capital σ)).mp ?_
  cases b
  · calc M.capital (σ ++ [false]) + M.capital σ
        ≤ M.capital (σ ++ [false]) + (M.capital (σ ++ [true]) + 1) :=
          add_le_add le_rfl (hs σ [true])
      _ = 2 * M.capital σ + 1 := by rw [← add_assoc, hfair]
      _ = M.capital σ + 1 + M.capital σ := by ring
  · calc M.capital (σ ++ [true]) + M.capital σ
        ≤ M.capital (σ ++ [true]) + (M.capital (σ ++ [false]) + 1) :=
          add_le_add le_rfl (hs σ [false])
      _ = 2 * M.capital σ + 1 := by
          rw [← add_assoc, add_comm (M.capital (σ ++ [true])), hfair]
      _ = M.capital σ + 1 + M.capital σ := by ring

/-- **Linear growth.** A martingale with savings gains at most one unit per bit. -/
theorem TreeMartingale.SavingsProperty.capital_le_root_add_length {M : TreeMartingale}
    (hs : M.SavingsProperty) (σ : BitString) :
    M.capital σ ≤ M.capital [] + (σ.length : ℚ≥0) := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b ih =>
    refine le_trans (capital_append_le_add_one hs σ b) ?_
    rw [List.length_append, List.length_singleton]
    push_cast
    calc M.capital σ + 1 ≤ M.capital [] + (σ.length : ℚ≥0) + 1 := add_le_add ih le_rfl
      _ = M.capital [] + ((σ.length : ℚ≥0) + 1) := by ring

/-- **Convergence.** With savings, success upgrades from unbounded to divergent: once the capital
reaches `c + 1` it never falls below `c` again. -/
theorem TreeMartingale.Succeeds.tendsto_atTop_of_savings {M : TreeMartingale} {x : Cantor}
    (h : M.Succeeds x) (hs : M.SavingsProperty) :
    Filter.Tendsto (fun n ↦ M.capital (initSeg x n)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro c
  obtain ⟨n, hn⟩ := h (c + 1)
  rw [Filter.eventually_atTop]
  refine ⟨n, fun m hm ↦ ?_⟩
  obtain ⟨τ, hτ⟩ := initSeg_prefix_of_le hm
  have hsav := hs (initSeg x n) τ
  rw [hτ] at hsav
  exact (add_le_add_iff_right 1).mp (le_trans hn hsav)

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

/-! ## Counting the banking events

Success is proved by counting. The identity below pins the source capital to the active account
and the number of banking events, and it holds *because* halving the active account and
incrementing the count cancel exactly — the same cancellation that makes fairness exact. -/

/-- A banking event occurs at `σ` on bit `b`. -/
def banked (M : TreeMartingale) (σ : BitString) (b : Bool) : Prop := 1 < nextActive M σ b

instance (M : TreeMartingale) (σ : BitString) (b : Bool) : Decidable (banked M σ b) :=
  inferInstanceAs (Decidable (1 < nextActive M σ b))

def bankCountStep (M : TreeMartingale) (q : BitString × ℕ) (b : Bool) : BitString × ℕ :=
  (q.1 ++ [b], if banked M q.1 b then q.2 + 1 else q.2)

def bankCountPair (M : TreeMartingale) (σ : BitString) : BitString × ℕ :=
  σ.foldl (bankCountStep M) ([], 0)

/-- The number of banking events on the way to `σ`. Proof-only. -/
def bankCount (M : TreeMartingale) (σ : BitString) : ℕ := (bankCountPair M σ).2

theorem foldl_bankCountStep_fst (M : TreeMartingale) (σ : BitString) :
    ∀ (τ : BitString) (k : ℕ), (σ.foldl (bankCountStep M) (τ, k)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ k; simp
  | cons b σ ih => intro τ k; rw [List.foldl_cons, ih]; simp [bankCountStep]

@[simp] theorem bankCountPair_fst (M : TreeMartingale) (σ : BitString) :
    (bankCountPair M σ).1 = σ := by
  rw [bankCountPair, foldl_bankCountStep_fst, List.nil_append]

@[simp] theorem bankCount_nil (M : TreeMartingale) : bankCount M [] = 0 := rfl

theorem bankCount_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    bankCount M (σ ++ [b]) = if banked M σ b then bankCount M σ + 1 else bankCount M σ := by
  have h : bankCountPair M (σ ++ [b]) = bankCountStep M (bankCountPair M σ) b := by
    rw [bankCountPair, bankCountPair, List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold bankCount
  rw [h, bankCountStep, bankCountPair_fst]

/-- The source capital, pinned to the active account and the banking count. Halving the active
account and incrementing the count cancel, so both branches give the same value. -/
theorem capital_eq_activePart_mul_pow (hpos : ∀ σ, 0 < M.capital σ) (σ : BitString) :
    M.capital σ = 2 * activePart M σ * M.capital [] * 2 ^ bankCount M σ := by
  induction σ using List.reverseRecOn with
  | nil => rw [activePart_nil, bankCount_nil]; norm_num
  | append_singleton σ b ih =>
    have hcancel : 2 * activePart M (σ ++ [b]) * M.capital [] * 2 ^ bankCount M (σ ++ [b])
        = 2 * nextActive M σ b * M.capital [] * 2 ^ bankCount M σ := by
      rw [active_append, bankCount_append]
      unfold banked
      split
      · rw [pow_succ]
        ring
      · rfl
    rw [hcancel, nextActive, bettingFactor]
    rw [show 2 * (activePart M σ * (M.capital (σ ++ [b]) / M.capital σ)) * M.capital []
          * 2 ^ bankCount M σ
        = (2 * activePart M σ * M.capital [] * 2 ^ bankCount M σ)
          * (M.capital (σ ++ [b]) / M.capital σ) by ring, ← ih]
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (hpos σ).ne', mul_one]

/-- Hence the source capital is bounded by the banking count. -/
theorem capital_le_pow_bankCount (hpos : ∀ σ, 0 < M.capital σ) (σ : BitString) :
    M.capital σ ≤ 2 * M.capital [] * 2 ^ bankCount M σ := by
  rw [capital_eq_activePart_mul_pow hpos σ]
  have hmul : 2 * activePart M σ * M.capital [] ≤ 2 * M.capital [] := by
    calc 2 * activePart M σ * M.capital [] ≤ 2 * 1 * M.capital [] := by
          gcongr; exact activePart_le_one hpos σ
      _ = 2 * M.capital [] := by ring
  gcongr

/-- Each banking event adds more than `1/2` to savings. -/
theorem half_bankCount_le_savingsPart (M : TreeMartingale) (σ : BitString) :
    (bankCount M σ : ℚ≥0) / 2 ≤ savingsPart M σ := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b ih =>
    rw [savings_append, bankCount_append]
    unfold banked
    split
    · rename_i hc
      rw [Nat.cast_add, Nat.cast_one, add_div]
      gcongr
    · exact ih

/-- Success of the source forces unboundedly many banking events. -/
theorem exists_bankCount_ge (hpos : ∀ σ, 0 < M.capital σ) {x : Cantor} (h : M.Succeeds x)
    (k : ℕ) : ∃ n, k ≤ bankCount M (initSeg x n) := by
  obtain ⟨n, hn⟩ := h (2 * M.capital [] * 2 ^ k + 1)
  refine ⟨n, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hle : M.capital (initSeg x n) ≤ 2 * M.capital [] * 2 ^ bankCount M (initSeg x n) :=
    capital_le_pow_bankCount hpos _
  have hpow : (2 : ℚ≥0) ^ bankCount M (initSeg x n) ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) hlt.le
  have : (2 : ℚ≥0) * M.capital [] * 2 ^ k + 1 ≤ 2 * M.capital [] * 2 ^ k := by
    refine hn.trans (hle.trans ?_)
    gcongr
  simp at this

/-- **Success preservation**: the normalization succeeds wherever the source does. -/
theorem savingsCapital_succeeds (hpos : ∀ σ, 0 < M.capital σ) {x : Cantor} (h : M.Succeeds x)
    (c : ℚ≥0) : ∃ n, c ≤ savingsCapital M (initSeg x n) := by
  obtain ⟨k, hk⟩ := exists_nat_ge ((2 * c : ℚ≥0) : ℝ)
  obtain ⟨n, hn⟩ := exists_bankCount_ge hpos h k
  refine ⟨n, ?_⟩
  have hck : c ≤ (k : ℚ≥0) / 2 := by
    rw [le_div_iff₀ two_pos, mul_comm]
    have : ((2 * c : ℚ≥0) : ℝ) ≤ ((k : ℚ≥0) : ℝ) := by exact_mod_cast hk
    exact_mod_cast this
  calc c ≤ (k : ℚ≥0) / 2 := hck
    _ ≤ (bankCount M (initSeg x n) : ℚ≥0) / 2 := by gcongr
    _ ≤ savingsPart M (initSeg x n) := half_bankCount_le_savingsPart M _
    _ ≤ savingsCapital M (initSeg x n) := savingsPart_le_savingsCapital M _

/-! ## The coded fold

The same walk, on codes. The state carries the prefix and the two accounts as `NNRatCode`
values, and the correspondence below is proved once at the level of the whole state; the
capital statement is then a projection rather than a second induction. -/

open Nat.Partrec (Code)

/-- The coded shifted capital of the source at `σ`. -/
def shiftedCode (p : Code) (s : ℕ) (σ : BitString) : ℕ :=
  NNRatCode.add (evalD p s (Encodable.encode σ)) (NNRatCode.ofNat 1)

/-- One step of the coded fold, mirroring `savingsStep`. -/
def savingsCodeStep (p : Code) (s : ℕ) (q : BitString × ℕ × ℕ) (b : Bool) : BitString × ℕ × ℕ :=
  let a' := NNRatCode.mul q.2.2
    (NNRatCode.div (shiftedCode p s (q.1 ++ [b])) (shiftedCode p s q.1))
  (q.1 ++ [b],
    if NNRatCode.lt (NNRatCode.ofNat 1) a' then (NNRatCode.add q.2.1 (NNRatCode.half a'),
      NNRatCode.half a') else (q.2.1, a'))

def savingsCodePair (p : Code) (s : ℕ) (σ : BitString) : BitString × ℕ × ℕ :=
  σ.foldl (savingsCodeStep p s) ([], (NNRatCode.ofNat 0, NNRatCode.half (NNRatCode.ofNat 1)))

/-- The coded capital: savings plus active, on codes. -/
def savingsCodeCapital (p : Code) (s : ℕ) (σ : BitString) : ℕ :=
  NNRatCode.add (savingsCodePair p s σ).2.1 (savingsCodePair p s σ).2.2

theorem savingsCodePair_append (p : Code) (s : ℕ) (σ : BitString) (b : Bool) :
    savingsCodePair p s (σ ++ [b]) = savingsCodeStep p s (savingsCodePair p s σ) b := by
  rw [savingsCodePair, savingsCodePair, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem foldl_savingsCodeStep_fst (p : Code) (s : ℕ) (σ : BitString) :
    ∀ (τ : BitString) (q : ℕ × ℕ), (σ.foldl (savingsCodeStep p s) (τ, q)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ q; simp
  | cons b σ ih => intro τ q; rw [List.foldl_cons, ih]; simp [savingsCodeStep]

@[simp] theorem savingsCodePair_fst (p : Code) (s : ℕ) (σ : BitString) :
    (savingsCodePair p s σ).1 = σ := by
  rw [savingsCodePair, foldl_savingsCodeStep_fst, List.nil_append]

/-! ## Correspondence

One statement covering both accounts, proved by a single induction; the capital statement is a
projection of it. The hypothesis is that the fuel suffices on every prefix involved, which the
totality of the source program supplies. -/

theorem shiftedCode_value {E : NatFunctionCode} {s : ℕ} {σ : BitString}
    (h : evalD E.program s (Encodable.encode σ) = E.toFun (Encodable.encode σ)) :
    NNRatCode.value (shiftedCode E.program s σ)
      = NNRatCode.value (E.toFun (Encodable.encode σ)) + 1 := by
  rw [shiftedCode, NNRatCode.value_add, h, NNRatCode.value_ofNat]
  norm_num

theorem shiftedCode_pos {E : NatFunctionCode} {s : ℕ} {σ : BitString}
    (h : evalD E.program s (Encodable.encode σ) = E.toFun (Encodable.encode σ)) :
    0 < NNRatCode.value (shiftedCode E.program s σ) := by
  rw [shiftedCode_value h]
  positivity

/-- The martingale a `ComputableMartingale` denotes, shifted to be positive. -/
theorem shift_capital_eq (M : ComputableMartingale) (σ : BitString) :
    M.toTreeMartingale.shift.capital σ
      = NNRatCode.value (M.program.toFun (Encodable.encode σ)) + 1 := by
  rw [TreeMartingale.shift_capital, M.eval_capital σ]

/-- **The state correspondence**: the coded fold decodes to the semantic accounts. -/
theorem savingsCodePair_value (M : ComputableMartingale) {s : ℕ} {σ : BitString}
    (hfuel : M.program.PathFuelOk s σ) :
    NNRatCode.value (savingsCodePair M.program.program s σ).2.1
        = savingsPart M.toTreeMartingale.shift σ ∧
      NNRatCode.value (savingsCodePair M.program.program s σ).2.2
        = activePart M.toTreeMartingale.shift σ := by
  induction σ using List.reverseRecOn with
  | nil =>
    have hs : (savingsCodePair M.program.program s []).2.1 = NNRatCode.ofNat 0 := rfl
    have ha : (savingsCodePair M.program.program s []).2.2
        = NNRatCode.half (NNRatCode.ofNat 1) := rfl
    refine ⟨?_, ?_⟩
    · rw [hs, NNRatCode.value_ofNat, savingsPart_nil]
      norm_num
    · rw [ha, NNRatCode.value_half, NNRatCode.value_ofNat, activePart_nil]
      norm_num
  | append_singleton σ b ih =>
    have hσ : M.program.PathFuelOk s σ := fun τ hτ ↦ hfuel τ (hτ.trans (List.prefix_append σ [b]))
    obtain ⟨ihs, iha⟩ := ih hσ
    have hev := hfuel σ (List.prefix_append σ [b])
    have hevb := hfuel (σ ++ [b]) (List.prefix_refl _)
    -- the coded next-active decodes to the semantic one
    have hden : 0 < NNRatCode.value (shiftedCode M.program.program s σ) := shiftedCode_pos hev
    have hnext : NNRatCode.value (NNRatCode.mul (savingsCodePair M.program.program s σ).2.2
        (NNRatCode.div (shiftedCode M.program.program s (σ ++ [b]))
          (shiftedCode M.program.program s σ)))
        = nextActive M.toTreeMartingale.shift σ b := by
      rw [NNRatCode.value_mul, NNRatCode.value_div hden, iha, nextActive, bettingFactor,
        shiftedCode_value hev, shiftedCode_value hevb, ← shift_capital_eq M,
        ← shift_capital_eq M]
    rw [savingsCodePair_append, savingsCodeStep, savingsCodePair_fst]
    rw [savings_append, active_append]
    by_cases hc : 1 < nextActive M.toTreeMartingale.shift σ b
    · have hlt : NNRatCode.lt (NNRatCode.ofNat 1)
          (NNRatCode.mul (savingsCodePair M.program.program s σ).2.2
            (NNRatCode.div (shiftedCode M.program.program s (σ ++ [b]))
              (shiftedCode M.program.program s σ))) = true := by
        rw [NNRatCode.lt_iff, NNRatCode.value_ofNat, hnext]
        exact_mod_cast hc
      rw [if_pos hlt, if_pos hc, if_pos hc]
      exact ⟨by rw [NNRatCode.value_add, NNRatCode.value_half, ihs, hnext],
        by rw [NNRatCode.value_half, hnext]⟩
    · have hlt : NNRatCode.lt (NNRatCode.ofNat 1)
          (NNRatCode.mul (savingsCodePair M.program.program s σ).2.2
            (NNRatCode.div (shiftedCode M.program.program s (σ ++ [b]))
              (shiftedCode M.program.program s σ))) = false := by
        rw [Bool.eq_false_iff, ne_eq, NNRatCode.lt_iff, NNRatCode.value_ofNat, hnext]
        exact_mod_cast hc
      rw [if_neg (by simp [hlt]), if_neg hc, if_neg hc]
      exact ⟨ihs, hnext⟩

/-- The capital statement, a projection of the state correspondence. -/
theorem savingsCodeCapital_value (M : ComputableMartingale) {s : ℕ} {σ : BitString}
    (hfuel : M.program.PathFuelOk s σ) :
    NNRatCode.value (savingsCodeCapital M.program.program s σ)
      = savingsCapital M.toTreeMartingale.shift σ := by
  obtain ⟨hs, ha⟩ := savingsCodePair_value M hfuel
  rw [savingsCodeCapital, NNRatCode.value_add, hs, ha, savingsCapital]

/-! ## Fuel search and extraction -/

-- Same proof-engineering boundary as elsewhere: the coded arithmetic unfolds into `Nat.unpair`
-- and hence `Nat.sqrt`, which makes elaboration explode during `Primrec` composition.
attribute [local irreducible] NNRatCode.add NNRatCode.mul NNRatCode.div NNRatCode.half
  NNRatCode.lt NNRatCode.ofNat

/-! ## The program -/

private theorem primrec_savingsCodeCapital :
    Primrec fun z : (Code × ℕ) × BitString ↦ savingsCodeCapital z.1.1 z.1.2 z.2 := by
  have hshift : Primrec fun v : ((Code × ℕ) × BitString) × BitString ↦
      shiftedCode v.1.1.1 v.1.1.2 v.2 := by
    unfold shiftedCode
    exact NNRatCode.primrec_add.comp
      (primrec_evalD.comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.encode.comp Primrec.snd)))
      (NNRatCode.primrec_ofNat.comp (Primrec.const 1))
  have hstep : Primrec₂ fun (z : (Code × ℕ) × BitString)
      (q : (BitString × ℕ × ℕ) × Bool) ↦ savingsCodeStep z.1.1 z.1.2 q.1 q.2 := by
    unfold savingsCodeStep
    have hpref : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × ℕ) × Bool) ↦
        v.2.1.1 ++ [v.2.2] :=
      Primrec.list_append.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    have hbase : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × ℕ) × Bool) ↦
        v.1 := Primrec.fst
    have hchild : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × ℕ) × Bool) ↦
        shiftedCode v.1.1.1 v.1.1.2 (v.2.1.1 ++ [v.2.2]) := hshift.comp (hbase.pair hpref)
    have hpar : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × ℕ) × Bool) ↦
        shiftedCode v.1.1.1 v.1.1.2 v.2.1.1 :=
      hshift.comp (hbase.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
    have ha' : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × ℕ) × Bool) ↦
        NNRatCode.mul v.2.1.2.2 (NNRatCode.div
          (shiftedCode v.1.1.1 v.1.1.2 (v.2.1.1 ++ [v.2.2]))
          (shiftedCode v.1.1.1 v.1.1.2 v.2.1.1)) :=
      NNRatCode.primrec_mul.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (NNRatCode.primrec_div.comp hchild hpar)
    refine Primrec₂.pair.comp hpref ?_
    refine Primrec.ite (Primrec.eq.comp
      (NNRatCode.primrec_lt.comp (NNRatCode.primrec_ofNat.comp (Primrec.const 1)) ha')
      (Primrec.const true)) ?_ ?_
    · exact Primrec₂.pair.comp
        (NNRatCode.primrec_add.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (NNRatCode.primrec_half.comp ha'))
        (NNRatCode.primrec_half.comp ha')
    · exact Primrec₂.pair.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) ha'
  have hfold : Primrec fun z : (Code × ℕ) × BitString ↦ savingsCodePair z.1.1 z.1.2 z.2 := by
    unfold savingsCodePair
    refine Primrec.list_foldl Primrec.snd ?_ hstep
    exact Primrec₂.pair.comp (Primrec.const [])
      (Primrec₂.pair.comp (Primrec.const (NNRatCode.ofNat 0))
        (Primrec.const (NNRatCode.half (NNRatCode.ofNat 1))))
  unfold savingsCodeCapital
  exact NNRatCode.primrec_add.comp
    (Primrec.fst.comp (Primrec.snd.comp hfold)) (Primrec.snd.comp (Primrec.snd.comp hfold))

/-- On input `encode σ`, the coded normalized capital at `σ`. -/
def savingsEnum (p : Code) : ℕ →. ℕ := fun input ↦
  (Nat.rfind fun s ↦ Part.some
      (pathFuelOk p s ((Encodable.decode input : Option BitString).getD []))).map
    fun s ↦ savingsCodeCapital p s ((Encodable.decode input : Option BitString).getD [])

/-- The primary computability statement, uniform in the raw source program. -/
theorem partrec_savingsEnumUniform : Partrec fun z : Code × ℕ ↦ savingsEnum z.1 z.2 := by
  have hstr : Primrec fun z : Code × ℕ ↦ (Encodable.decode z.2 : Option BitString).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const [])
  have hok : Primrec fun q : (Code × ℕ) × ℕ ↦
      pathFuelOk q.1.1 q.2 ((Encodable.decode q.1.2 : Option BitString).getD []) :=
    primrec_pathFuelOk.comp
      (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair (hstr.comp Primrec.fst))
  have hval : Primrec fun q : (Code × ℕ) × ℕ ↦
      savingsCodeCapital q.1.1 q.2 ((Encodable.decode q.1.2 : Option BitString).getD []) :=
    primrec_savingsCodeCapital.comp
      (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair (hstr.comp Primrec.fst))
  exact Partrec.map (Partrec.rfind (Computable₂.partrec₂ hok.to_comp.to₂)) hval.to_comp.to₂

theorem partrec_savingsEnum (p : Code) : Nat.Partrec (savingsEnum p) :=
  Partrec.nat_iff.mp ((partrec_savingsEnumUniform.comp
    (Computable.pair (Computable.const p) Computable.id)).of_eq fun _ ↦ rfl)

/-! ## The bundled normalization -/

/-- A computable martingale with the savings property. -/
structure SavingsComputableMartingale extends ComputableMartingale where
  /-- The capital never falls more than `1` below any earlier value. -/
  savingsProperty : toTreeMartingale.SavingsProperty

namespace ComputableMartingale

variable (M : ComputableMartingale)

theorem savingsEnum_dom (input : ℕ) : (savingsEnum M.program.program input).Dom := by
  obtain ⟨s, hs⟩ :=
    exists_pathFuelOk M.program ((Encodable.decode input : Option BitString).getD [])
  obtain ⟨t, htmem, -⟩ := Nat.rfind_min'
    (p := fun s ↦ pathFuelOk M.program.program s
      ((Encodable.decode input : Option BitString).getD [])) (m := s) hs
  exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ htmem⟩

/-- The program computing the normalized capital. -/
noncomputable def savingsFunctionCode : NatFunctionCode :=
  NatFunctionCode.ofPartrecTotal (partrec_savingsEnum M.program.program) M.savingsEnum_dom

theorem savingsFunctionCode_value (σ : BitString) :
    NNRatCode.value (M.savingsFunctionCode.toFun (Encodable.encode σ))
      = savingsCapital M.toTreeMartingale.shift σ := by
  have hmem : M.savingsFunctionCode.toFun (Encodable.encode σ)
      ∈ savingsEnum M.program.program (Encodable.encode σ) := by
    rw [savingsFunctionCode, NatFunctionCode.ofPartrecTotal_toFun]
    exact Part.get_mem _
  rw [savingsEnum, Encodable.encodek, Option.getD_some, Part.mem_map_iff] at hmem
  obtain ⟨s, hs, hval⟩ := hmem
  have hok : pathFuelOk M.program.program s σ = true := by
    have := Nat.rfind_spec hs; simpa using this
  rw [← hval]
  exact savingsCodeCapital_value M (pathFuelOk_spec hok)

/-- **The savings normalization**: uniform in `M`, with no reference to any path. -/
noncomputable def withSavings : SavingsComputableMartingale where
  capital := savingsCapital M.toTreeMartingale.shift
  fair := savingsCapital_fair M.toTreeMartingale.shift_pos
  program := M.savingsFunctionCode
  eval_capital := M.savingsFunctionCode_value
  savingsProperty := savingsCapital_savings M.toTreeMartingale.shift_pos

@[simp] theorem withSavings_capital (σ : BitString) :
    M.withSavings.capital σ = savingsCapital M.toTreeMartingale.shift σ := rfl

/-- Success is preserved, for every path. -/
theorem succeeds_withSavings {x : Cantor} (h : M.Succeeds x) : M.withSavings.Succeeds x := by
  intro c
  exact savingsCapital_succeeds M.toTreeMartingale.shift_pos
    (TreeMartingale.succeeds_shift h) c

end ComputableMartingale

end AlgorithmicRandomness
