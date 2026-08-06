/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.RatCode
import AlgorithmicRandomness.Martingale.Savings

/-!
# The bounded oscillating martingale

From a martingale with the savings property, build a bounded one that oscillates between values
at most `2` and values at least `3` along every path where the source succeeds. This converts
*divergence* of the source into *bounded oscillation*, which is what a Lipschitz function's
slope process can exhibit.

Following Freer–Kjos-Hanssen–Nies–Stephan, Theorem 4.2. The construction is a single martingale
carrying a phase bit, updated **additively** by the source's capital increment: in the up phase
it adds what the source risks until reaching `3`, in the down phase it subtracts until reaching
`2`, clipping exactly at the threshold and sending the clipped child into the opposite phase.

The four constants are not interchangeable. A fair martingale confined to `[c, d]` that
*attains* an endpoint is frozen there — both children must average to the endpoint while
staying inside — so it could never oscillate. Here the oscillation targets `2` and `3` are
interior to the hard bounds `[1, 4]`, which is exactly what leaves room to keep moving. The
bounds themselves come from the savings property, not from positivity.

## Representation

The recursion is stated on `ℚ`, not `ℚ≥0`: the update subtracts, and truncated subtraction
would contaminate every semantic proof. The nonnegativity needed to package the result is a
*theorem* about the raw recursion, proved from the bounds.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-- The capital increment of `M` at `σ` on bit `b`, as a signed rational. -/
def increment (M : TreeMartingale) (σ : BitString) (b : Bool) : ℚ :=
  ((M.capital (σ ++ [b]) : ℚ≥0) : ℚ) - ((M.capital σ : ℚ≥0) : ℚ)

/-- The two increments cancel, because the source is a martingale. -/
theorem increment_add (M : TreeMartingale) (σ : BitString) :
    increment M σ false + increment M σ true = 0 := by
  have h : ((M.capital (σ ++ [false]) : ℚ≥0) : ℚ) + ((M.capital (σ ++ [true]) : ℚ≥0) : ℚ)
      = 2 * ((M.capital σ : ℚ≥0) : ℚ) := by exact_mod_cast M.fair σ
  rw [increment, increment]
  linarith

theorem increment_neg (M : TreeMartingale) (σ : BitString) (b : Bool) :
    increment M σ (!b) = -increment M σ b := by
  have h := increment_add M σ
  cases b <;> simp only [Bool.not_false, Bool.not_true] <;> linarith

/-! ## The raw recursion

Each step is local in the bit: the sibling's value is `2 v - r`, so whether the sibling clips
is decidable from `r` and `v` alone. -/

/-- One step. The phase is `true` for up, `false` for down. -/
def oscStep (M : TreeMartingale) (q : BitString × ℚ × Bool) (b : Bool) : BitString × ℚ × Bool :=
  if q.2.2 then
    -- up phase: this child's value is `v + d`, the sibling's is `v - d`
    if 3 ≤ q.2.1 + increment M q.1 b then (q.1 ++ [b], 3, false)
    else if 3 ≤ q.2.1 - increment M q.1 b then (q.1 ++ [b], 2 * q.2.1 - 3, true)
    else (q.1 ++ [b], q.2.1 + increment M q.1 b, true)
  else
    -- down phase: this child's value is `v - d`, the sibling's is `v + d`
    if q.2.1 - increment M q.1 b ≤ 2 then (q.1 ++ [b], 2, true)
    else if q.2.1 + increment M q.1 b ≤ 2 then (q.1 ++ [b], 2 * q.2.1 - 2, false)
    else (q.1 ++ [b], q.2.1 - increment M q.1 b, false)

def oscPair (M : TreeMartingale) (σ : BitString) : BitString × ℚ × Bool :=
  σ.foldl (oscStep M) ([], (2, true))

/-- The value of the oscillating martingale at `σ`, before any conversion. -/
def rawValue (M : TreeMartingale) (σ : BitString) : ℚ := (oscPair M σ).2.1

/-- The phase at `σ`: `true` is the up phase, `false` the down phase. -/
def phase (M : TreeMartingale) (σ : BitString) : Bool := (oscPair M σ).2.2

/-- Every branch of the step extends the prefix by the bit. -/
theorem oscStep_fst (M : TreeMartingale) (q : BitString × ℚ × Bool) (b : Bool) :
    (oscStep M q b).1 = q.1 ++ [b] := by
  rw [oscStep]
  split
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem foldl_oscStep_fst (M : TreeMartingale) (σ : BitString) :
    ∀ (τ : BitString) (q : ℚ × Bool), (σ.foldl (oscStep M) (τ, q)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ q; simp
  | cons b σ ih =>
    intro τ q
    rw [List.foldl_cons, ih, oscStep_fst]
    simp

@[simp] theorem oscPair_fst (M : TreeMartingale) (σ : BitString) : (oscPair M σ).1 = σ := by
  rw [oscPair, foldl_oscStep_fst, List.nil_append]

theorem oscPair_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    oscPair M (σ ++ [b]) = oscStep M (oscPair M σ) b := by
  rw [oscPair, oscPair, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem rawValue_nil (M : TreeMartingale) : rawValue M [] = 2 := rfl
@[simp] theorem phase_nil (M : TreeMartingale) : phase M [] = true := rfl

/-- The step, written out at `σ ++ [b]`. -/
theorem oscPair_append_eq (M : TreeMartingale) (σ : BitString) (b : Bool) :
    (rawValue M (σ ++ [b]), phase M (σ ++ [b]))
      = (if phase M σ then
          (if 3 ≤ rawValue M σ + increment M σ b then ((3 : ℚ), false)
           else if 3 ≤ rawValue M σ - increment M σ b then (2 * rawValue M σ - 3, true)
           else (rawValue M σ + increment M σ b, true))
        else
          (if rawValue M σ - increment M σ b ≤ 2 then ((2 : ℚ), true)
           else if rawValue M σ + increment M σ b ≤ 2 then (2 * rawValue M σ - 2, false)
           else (rawValue M σ - increment M σ b, false))) := by
  have h : oscPair M (σ ++ [b]) = oscStep M (oscPair M σ) b := oscPair_append M σ b
  unfold rawValue phase
  rw [h, oscStep, oscPair_fst]
  split
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl

end AlgorithmicRandomness
