/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.NNRatCode
import Mathlib.Tactic.Linarith

/-!
# Coded signed rationals

A signed rational is coded as a **pair of coded nonnegative rationals**, a positive part and a
negative part, with value their difference in `ℚ`. Subtraction is then just swapping the two
parts before adding, and every operation stays primitive recursive.

This layer is kept separate from `NNRatCode` on purpose: the invariants differ. `NNRatCode`
values are nonnegative by type, whereas here nonnegativity is a *proved property* of particular
values, and `toNNRat` converts across that boundary only under an explicit hypothesis. Every
semantic statement casts `NNRatCode.value` into `ℚ` before subtracting, so truncated `ℚ≥0`
subtraction can never sneak in.

The one operation shaped by the intended application is `childUpdate`, which sends a parent
value `x` to `x + (a - b)/2` and `x + (b - a)/2` on the two children — an update that is exactly
fair by construction, whatever the approximations `a` and `b` happen to be.
-/

open scoped NNRat

namespace AlgorithmicRandomness
namespace RatCode

/-- The signed rational coded by a natural: the difference of its two coded parts. -/
def value (m : ℕ) : ℚ := (NNRatCode.value m.unpair.1 : ℚ) - (NNRatCode.value m.unpair.2 : ℚ)

theorem value_pair (a b : ℕ) :
    value (Nat.pair a b) = (NNRatCode.value a : ℚ) - (NNRatCode.value b : ℚ) := by
  rw [value, Nat.unpair_pair]

/-- A nonnegative coded rational, viewed as a signed one. -/
def ofNNRat (q : ℕ) : ℕ := Nat.pair q (Nat.pair 0 0)

@[simp] theorem value_ofNNRat (q : ℕ) : value (ofNNRat q) = (NNRatCode.value q : ℚ) := by
  rw [ofNNRat, value_pair, NNRatCode.value_pair_zero]
  simp

/-- A natural, viewed as a signed coded rational. -/
def ofNat (k : ℕ) : ℕ := ofNNRat (Nat.pair k 0)

@[simp] theorem value_ofNat (k : ℕ) : value (ofNat k) = (k : ℚ) := by
  rw [ofNat, value_ofNNRat, NNRatCode.value_pair_zero]
  push_cast
  rfl

def neg (m : ℕ) : ℕ := Nat.pair m.unpair.2 m.unpair.1

@[simp] theorem value_neg (m : ℕ) : value (neg m) = -value m := by
  rw [neg, value_pair, value]
  ring

def add (m n : ℕ) : ℕ :=
  Nat.pair (NNRatCode.add m.unpair.1 n.unpair.1) (NNRatCode.add m.unpair.2 n.unpair.2)

@[simp] theorem value_add (m n : ℕ) : value (add m n) = value m + value n := by
  rw [add, value_pair, NNRatCode.value_add, NNRatCode.value_add, value, value]
  push_cast
  ring

def sub (m n : ℕ) : ℕ := add m (neg n)

@[simp] theorem value_sub (m n : ℕ) : value (sub m n) = value m - value n := by
  rw [sub, value_add, value_neg]
  ring

def double (m : ℕ) : ℕ :=
  Nat.pair (NNRatCode.double m.unpair.1) (NNRatCode.double m.unpair.2)

@[simp] theorem value_double (m : ℕ) : value (double m) = 2 * value m := by
  rw [double, value_pair, NNRatCode.value_double, NNRatCode.value_double, value]
  push_cast
  ring

def half (m : ℕ) : ℕ := Nat.pair (NNRatCode.half m.unpair.1) (NNRatCode.half m.unpair.2)

@[simp] theorem value_half (m : ℕ) : value (half m) = value m / 2 := by
  rw [half, value_pair, NNRatCode.value_half, NNRatCode.value_half, value]
  push_cast
  ring

/-! ## The child update

`childUpdate x a b` moves the parent value `x` to the child selected by the bit, adding half the
signed gap between the two approximations. Whatever `a` and `b` are, the two children sum to
`2 * x`: fairness is definitional, not approximate. -/

def childUpdate (x a b : ℕ) (bit : Bool) : ℕ :=
  add x (half (if bit then sub (ofNNRat b) (ofNNRat a) else sub (ofNNRat a) (ofNNRat b)))

theorem value_childUpdate_false (x a b : ℕ) :
    value (childUpdate x a b false)
      = value x + ((NNRatCode.value a : ℚ) - (NNRatCode.value b : ℚ)) / 2 := by
  rw [childUpdate, if_neg (by simp), value_add, value_half, value_sub, value_ofNNRat,
    value_ofNNRat]

theorem value_childUpdate_true (x a b : ℕ) :
    value (childUpdate x a b true)
      = value x + ((NNRatCode.value b : ℚ) - (NNRatCode.value a : ℚ)) / 2 := by
  rw [childUpdate, if_pos rfl, value_add, value_half, value_sub, value_ofNNRat, value_ofNNRat]

/-- Exact fairness of the child update, for arbitrary approximations. -/
theorem value_childUpdate_add (x a b : ℕ) :
    value (childUpdate x a b false) + value (childUpdate x a b true) = 2 * value x := by
  rw [value_childUpdate_false, value_childUpdate_true]
  ring

/-! ## Comparison

Clipping decisions consult these rather than the signed representation: `m ≤ n` is decided as
`m⁺ + n⁻ ≤ n⁺ + m⁻`, entirely inside the nonnegative layer. -/

def le (m n : ℕ) : Bool :=
  NNRatCode.le (NNRatCode.add m.unpair.1 n.unpair.2) (NNRatCode.add n.unpair.1 m.unpair.2)

theorem le_iff (m n : ℕ) : le m n = true ↔ value m ≤ value n := by
  rw [le, NNRatCode.le_iff, NNRatCode.value_add, NNRatCode.value_add, value, value]
  constructor
  · intro h
    have h' : ((NNRatCode.value m.unpair.1 : ℚ)) + (NNRatCode.value n.unpair.2 : ℚ)
        ≤ (NNRatCode.value n.unpair.1 : ℚ) + (NNRatCode.value m.unpair.2 : ℚ) := by
      exact_mod_cast h
    linarith
  · intro h
    have h' : ((NNRatCode.value m.unpair.1 : ℚ)) + (NNRatCode.value n.unpair.2 : ℚ)
        ≤ (NNRatCode.value n.unpair.1 : ℚ) + (NNRatCode.value m.unpair.2 : ℚ) := by linarith
    exact_mod_cast h'

def lt (m n : ℕ) : Bool := !(le n m)

theorem lt_iff (m n : ℕ) : lt m n = true ↔ value m < value n := by
  rw [lt, Bool.not_eq_true', ← not_le, ← le_iff n m]
  simp

theorem primrec_le : Primrec₂ le :=
  NNRatCode.primrec_le.comp
    (NNRatCode.primrec_add.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    (NNRatCode.primrec_add.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))

theorem primrec_lt : Primrec₂ lt := Primrec.not.comp (primrec_le.comp Primrec.snd Primrec.fst)

/-! ## Back to the nonnegative layer -/

/-- Convert a signed code to a nonnegative one. Correct exactly when the value is nonnegative,
which is what licenses the truncated `ℕ` subtraction in the numerator. -/
def toNNRat (m : ℕ) : ℕ :=
  Nat.pair
    (m.unpair.1.unpair.1 * (m.unpair.2.unpair.2 + 1)
      - m.unpair.2.unpair.1 * (m.unpair.1.unpair.2 + 1))
    ((m.unpair.1.unpair.2 + 1) * (m.unpair.2.unpair.2 + 1) - 1)

/-- Cast a coded value into `ℚ` with the numerator kept opaque, so that a `ℕ` subtraction inside
it is never pushed into a truncated `ℚ≥0` one. -/
private theorem coe_value_pair_sub_one {N D : ℕ} (hD : 0 < D) :
    ((NNRatCode.value (Nat.pair N (D - 1)) : ℚ)) = (N : ℚ) / (D : ℚ) := by
  rw [NNRatCode.value_pair, Nat.sub_add_cancel hD]
  push_cast
  rfl

theorem value_toNNRat {m : ℕ} (h : 0 ≤ value m) :
    (NNRatCode.value (toNNRat m) : ℚ) = value m := by
  set p := m.unpair.1.unpair.1 with hp
  set a := m.unpair.1.unpair.2 with ha
  set q := m.unpair.2.unpair.1 with hq
  set b := m.unpair.2.unpair.2 with hb
  have hposa : (0 : ℚ) < ((a + 1 : ℕ) : ℚ) := by positivity
  have hposb : (0 : ℚ) < ((b + 1 : ℕ) : ℚ) := by positivity
  have hval : value m = (p : ℚ) / ((a + 1 : ℕ) : ℚ) - (q : ℚ) / ((b + 1 : ℕ) : ℚ) := by
    rw [value, NNRatCode.value, NNRatCode.value]
    push_cast
    ring
  -- nonnegativity of the value is exactly nonnegativity of the cross-multiplied numerator
  have hnum : q * (a + 1) ≤ p * (b + 1) := by
    rw [hval, sub_nonneg, div_le_div_iff₀ hposb hposa] at h
    exact_mod_cast h
  have hposab : 0 < (a + 1) * (b + 1) := Nat.mul_pos a.succ_pos b.succ_pos
  -- take the cast through the division with the numerator opaque, then subtract in `ℚ`
  rw [toNNRat, coe_value_pair_sub_one hposab, Nat.cast_sub hnum, hval]
  push_cast
  field_simp

/-! ## Computability -/

theorem primrec_ofNNRat : Primrec ofNNRat :=
  Primrec₂.natPair.comp Primrec.id (Primrec.const (Nat.pair 0 0))

theorem primrec_neg : Primrec neg :=
  Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)

theorem primrec_add : Primrec₂ add :=
  Primrec₂.natPair.comp
    (NNRatCode.primrec_add.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
    (NNRatCode.primrec_add.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))

theorem primrec_sub : Primrec₂ sub := primrec_add.comp Primrec.fst (primrec_neg.comp Primrec.snd)

theorem primrec_double : Primrec double :=
  Primrec₂.natPair.comp (NNRatCode.primrec_double.comp (Primrec.fst.comp Primrec.unpair))
    (NNRatCode.primrec_double.comp (Primrec.snd.comp Primrec.unpair))

theorem primrec_ofNat : Primrec ofNat :=
  primrec_ofNNRat.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const 0))

theorem primrec_half : Primrec half :=
  Primrec₂.natPair.comp (NNRatCode.primrec_half.comp (Primrec.fst.comp Primrec.unpair))
    (NNRatCode.primrec_half.comp (Primrec.snd.comp Primrec.unpair))

theorem primrec_childUpdate :
    Primrec fun z : (ℕ × ℕ × ℕ) × Bool ↦ childUpdate z.1.1 z.1.2.1 z.1.2.2 z.2 := by
  unfold childUpdate
  refine primrec_add.comp (Primrec.fst.comp Primrec.fst) (primrec_half.comp ?_)
  refine Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true)) ?_ ?_
  · exact primrec_sub.comp (primrec_ofNNRat.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (primrec_ofNNRat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  · exact primrec_sub.comp (primrec_ofNNRat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (primrec_ofNNRat.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

theorem primrec_toNNRat : Primrec toNNRat := by
  have hp : Primrec fun m : ℕ ↦ m.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have ha : Primrec fun m : ℕ ↦ m.unpair.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hq : Primrec fun m : ℕ ↦ m.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hb : Primrec fun m : ℕ ↦ m.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact Primrec₂.natPair.comp
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp hp (Primrec.succ.comp hb))
      (Primrec.nat_mul.comp hq (Primrec.succ.comp ha)))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.succ.comp ha) (Primrec.succ.comp hb))
      (Primrec.const 1))

/-! ## Clamping into the unit interval

The result is a *nonnegative* code: the clamp is nonnegative by construction, and both consumers —
the dyadic floor and scaling by a natural — live in the nonnegative layer. The truncated `ℚ≥0`
subtraction stays inside that layer; the statement below is in `ℚ`, with `max` and `min`. -/

/-- The clamp of a signed coded rational into `[0, 1]`, as a coded nonnegative rational. -/
def clampUnit (m : ℕ) : ℕ :=
  if NNRatCode.le (NNRatCode.sub m.unpair.1 m.unpair.2) (NNRatCode.ofNat 1) then
    NNRatCode.sub m.unpair.1 m.unpair.2
  else NNRatCode.ofNat 1

private theorem coe_value_sub_parts (m : ℕ) :
    ((NNRatCode.value (NNRatCode.sub m.unpair.1 m.unpair.2) : ℚ≥0) : ℚ) = max 0 (value m) := by
  rw [NNRatCode.value_sub]
  rcases le_total (NNRatCode.value m.unpair.2) (NNRatCode.value m.unpair.1) with h | h
  · rw [NNRat.coe_sub h, value, max_eq_right (by
      have : ((NNRatCode.value m.unpair.2 : ℚ≥0) : ℚ) ≤ (NNRatCode.value m.unpair.1 : ℚ≥0) := by
        exact_mod_cast h
      linarith)]
  · rw [tsub_eq_zero_of_le h, NNRat.cast_zero, value, max_eq_left (by
      have : ((NNRatCode.value m.unpair.1 : ℚ≥0) : ℚ) ≤ (NNRatCode.value m.unpair.2 : ℚ≥0) := by
        exact_mod_cast h
      linarith)]

theorem value_clampUnit (m : ℕ) :
    ((NNRatCode.value (clampUnit m) : ℚ≥0) : ℚ) = max 0 (min 1 (value m)) := by
  rw [clampUnit]
  by_cases hc : NNRatCode.le (NNRatCode.sub m.unpair.1 m.unpair.2) (NNRatCode.ofNat 1) = true
  · rw [if_pos hc, coe_value_sub_parts]
    have h1 : NNRatCode.value (NNRatCode.sub m.unpair.1 m.unpair.2) ≤ 1 := by
      have := (NNRatCode.le_iff _ _).mp hc
      simpa using this
    have h2 : max 0 (value m) ≤ 1 := by
      rw [← coe_value_sub_parts m]
      exact_mod_cast h1
    rw [min_eq_right (le_trans (le_max_right 0 (value m)) h2)]
  · rw [if_neg hc, NNRatCode.value_ofNat, Nat.cast_one, NNRat.cast_one]
    have h1 : ¬NNRatCode.value (NNRatCode.sub m.unpair.1 m.unpair.2) ≤ 1 := by
      intro hle
      exact hc ((NNRatCode.le_iff _ _).mpr (by simpa using hle))
    have h2 : (1 : ℚ) < max 0 (value m) := by
      rw [← coe_value_sub_parts m]
      exact_mod_cast lt_of_not_ge h1
    have h3 : (1 : ℚ) ≤ value m := le_of_lt (by
      rcases max_cases (0 : ℚ) (value m) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at h2 <;> linarith)
    rw [min_eq_left h3, max_eq_right (by linarith : (0:ℚ) ≤ 1)]

theorem primrec_clampUnit : Primrec clampUnit := by
  have hsub : Primrec fun m : ℕ ↦ NNRatCode.sub m.unpair.1 m.unpair.2 :=
    NNRatCode.primrec_sub.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)
  have hcond := Primrec.cond
    (NNRatCode.primrec_le.comp hsub (Primrec.const (NNRatCode.ofNat 1))) hsub
    (Primrec.const (NNRatCode.ofNat 1))
  exact hcond.of_eq fun m ↦ by rw [clampUnit, Bool.cond_eq_ite]

end RatCode
end AlgorithmicRandomness
