/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coded nonnegative rationals

Mathlib provides no `Primcodable ℚ≥0`, so a program cannot output a `ℚ≥0` in any way that later
coded constructions could consume. Instead a program outputs a **natural encoding a nonnegative
rational**: `Nat.pair num (den - 1)`, with the denominator stored shifted so that *every*
natural decodes and the representation is total.

The adequacy criterion for downstream use is `NNRatCode.le`: comparison of two coded rationals
is decided in `ℕ` by cross-multiplication and is primitive recursive (`primrec_le`), exactly as
finite-open weight comparison was. An `Encodable ℚ≥0` output would fail here, since `Encodable`
supplies no primitive recursive comparison, so a coded threshold test could not be run inside a
program.
-/

open scoped NNRat

namespace AlgorithmicRandomness
namespace NNRatCode

/-- The nonnegative rational encoded by a natural: numerator and denominator-minus-one. -/
def value (m : ℕ) : ℚ≥0 := (m.unpair.1 : ℚ≥0) / ((m.unpair.2 + 1 : ℕ) : ℚ≥0)

theorem value_pair (a b : ℕ) : value (Nat.pair a b) = (a : ℚ≥0) / ((b + 1 : ℕ) : ℚ≥0) := by
  rw [value, Nat.unpair_pair]

@[simp] theorem value_pair_zero (a : ℕ) : value (Nat.pair a 0) = (a : ℚ≥0) := by
  rw [value_pair]
  norm_num

/-- Every nonnegative rational is coded. -/
theorem value_surjective (q : ℚ≥0) : ∃ m, value m = q := by
  refine ⟨Nat.pair q.num (q.den - 1), ?_⟩
  rw [value_pair, Nat.sub_add_cancel q.den_pos]
  exact q.num_div_den

/-! ## Arithmetic on codes -/

/-- Addition of coded rationals, by cross-multiplication onto a common denominator. -/
def add (m n : ℕ) : ℕ :=
  Nat.pair (m.unpair.1 * (n.unpair.2 + 1) + n.unpair.1 * (m.unpair.2 + 1))
    ((m.unpair.2 + 1) * (n.unpair.2 + 1) - 1)

theorem value_add (m n : ℕ) : value (add m n) = value m + value n := by
  have hpos : 0 < (m.unpair.2 + 1) * (n.unpair.2 + 1) := Nat.mul_pos m.unpair.2.succ_pos
    n.unpair.2.succ_pos
  rw [add, value_pair, Nat.sub_add_cancel hpos, value, value]
  have h1 : ((m.unpair.2 + 1 : ℕ) : ℚ≥0) ≠ 0 := by positivity
  have h2 : ((n.unpair.2 + 1 : ℕ) : ℚ≥0) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Doubling a coded rational. -/
def double (m : ℕ) : ℕ := Nat.pair (2 * m.unpair.1) m.unpair.2

theorem value_double (m : ℕ) : value (double m) = 2 * value m := by
  rw [double, value_pair, value]
  push_cast
  ring

/-- Halving a coded rational. -/
def half (m : ℕ) : ℕ := Nat.pair m.unpair.1 (2 * (m.unpair.2 + 1) - 1)

theorem value_half (m : ℕ) : value (half m) = value m / 2 := by
  have hpos : 0 < 2 * (m.unpair.2 + 1) := Nat.mul_pos two_pos m.unpair.2.succ_pos
  rw [half, value_pair, Nat.sub_add_cancel hpos, value]
  have h1 : ((m.unpair.2 + 1 : ℕ) : ℚ≥0) ≠ 0 := by positivity
  push_cast
  field_simp

theorem primrec_add : Primrec₂ add :=
  Primrec₂.natPair.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      (Primrec.const 1))

theorem primrec_double : Primrec double :=
  Primrec₂.natPair.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair)

theorem primrec_half : Primrec half :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.const 1))

/-- Multiplication of coded rationals. -/
def mul (m k : ℕ) : ℕ :=
  Nat.pair (m.unpair.1 * k.unpair.1) ((m.unpair.2 + 1) * (k.unpair.2 + 1) - 1)

theorem value_mul (m k : ℕ) : value (mul m k) = value m * value k := by
  have hpos : 0 < (m.unpair.2 + 1) * (k.unpair.2 + 1) :=
    Nat.mul_pos m.unpair.2.succ_pos k.unpair.2.succ_pos
  rw [mul, value_pair, Nat.sub_add_cancel hpos, value, value]
  push_cast
  rw [div_mul_div_comm]

theorem primrec_mul : Primrec₂ mul :=
  Primrec₂.natPair.comp
    (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      (Primrec.const 1))

@[simp] theorem value_eq_zero_iff (m : ℕ) : value m = 0 ↔ m.unpair.1 = 0 := by
  rw [value, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h (by positivity)
  · intro h
    exact Or.inl (by exact_mod_cast h)

@[simp] theorem value_pos_iff (m : ℕ) : 0 < value m ↔ 0 < m.unpair.1 := by
  rw [pos_iff_ne_zero, pos_iff_ne_zero, ne_eq, ne_eq, value_eq_zero_iff]

/-- Division of coded rationals, correct when the divisor is nonzero. -/
def div (m k : ℕ) : ℕ :=
  Nat.pair (m.unpair.1 * (k.unpair.2 + 1)) ((m.unpair.2 + 1) * k.unpair.1 - 1)

private theorem value_div_of_num_pos {m k : ℕ} (h : 0 < k.unpair.1) :
    value (div m k) = value m / value k := by
  have hpos : 0 < (m.unpair.2 + 1) * k.unpair.1 := Nat.mul_pos m.unpair.2.succ_pos h
  have hk : ((k.unpair.1 : ℚ≥0)) ≠ 0 := by
    simpa using (Nat.cast_pos (α := ℚ≥0)).mpr h |>.ne'
  rw [div, value_pair, Nat.sub_add_cancel hpos, value, value]
  push_cast
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm]
  field_simp

/-- Correctness of division, stated against the *decoded* divisor so that consumers never
unfold the representation. -/
theorem value_div {m k : ℕ} (hk : 0 < value k) : value (div m k) = value m / value k :=
  value_div_of_num_pos ((value_pos_iff k).mp hk)

theorem primrec_div : Primrec₂ div :=
  Primrec₂.natPair.comp
    (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
      (Primrec.const 1))

/-- Scaling a coded rational by a power of two, which is what a cylinder factor `2^|σ|` is. -/
def scalePowTwo (k m : ℕ) : ℕ := Nat.pair (2 ^ k * m.unpair.1) m.unpair.2

theorem value_scalePowTwo (k m : ℕ) : value (scalePowTwo k m) = 2 ^ k * value m := by
  rw [scalePowTwo, value_pair, value]
  push_cast
  ring

theorem primrec_scalePowTwo : Primrec₂ scalePowTwo :=
  Primrec₂.natPair.comp
    (Primrec.nat_mul.comp
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))

/-- Dividing a coded rational by a power of two, which is what a cell's measure `2^-n` is. The
denominator is stored shifted, so scaling it is `2 ^ k * (d + 1) - 1`; the subtraction is exact
because `2 ^ k * (d + 1)` is positive. -/
def divPowTwo (k m : ℕ) : ℕ := Nat.pair m.unpair.1 (2 ^ k * (m.unpair.2 + 1) - 1)

theorem value_divPowTwo (k m : ℕ) : value (divPowTwo k m) = value m / 2 ^ k := by
  have hpos : 0 < 2 ^ k * (m.unpair.2 + 1) := Nat.mul_pos (Nat.two_pow_pos k) m.unpair.2.succ_pos
  rw [divPowTwo, value_pair, Nat.sub_add_cancel hpos, value, div_div]
  push_cast
  ring_nf

theorem primrec_divPowTwo : Primrec₂ divPowTwo :=
  Primrec₂.natPair.comp
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp
        ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      (Primrec.const 1))

/-- Comparison of coded rationals, decided in `ℕ` by cross-multiplication. -/
def le (m k : ℕ) : Bool :=
  decide (m.unpair.1 * (k.unpair.2 + 1) ≤ k.unpair.1 * (m.unpair.2 + 1))

theorem le_iff (m k : ℕ) : le m k = true ↔ value m ≤ value k := by
  have hm : (0 : ℚ≥0) < ((m.unpair.2 + 1 : ℕ) : ℚ≥0) := by positivity
  have hk : (0 : ℚ≥0) < ((k.unpair.2 + 1 : ℕ) : ℚ≥0) := by positivity
  rw [le, decide_eq_true_iff, value, value, div_le_div_iff₀ hm hk]
  constructor
  · intro h
    exact_mod_cast (Nat.cast_le (α := ℚ≥0)).mpr h
  · intro h
    have : ((m.unpair.1 * (k.unpair.2 + 1) : ℕ) : ℚ≥0)
        ≤ ((k.unpair.1 * (m.unpair.2 + 1) : ℕ) : ℚ≥0) := by push_cast; exact_mod_cast h
    exact_mod_cast this

/-- Strict comparison, as the negation of the reverse comparison. -/
def lt (m k : ℕ) : Bool := !(le k m)

theorem lt_iff (m k : ℕ) : lt m k = true ↔ value m < value k := by
  rw [lt, Bool.not_eq_true', ← not_le, ← le_iff k m]
  simp

/-- A natural, as a coded rational. -/
def ofNat (k : ℕ) : ℕ := Nat.pair k 0

@[simp] theorem value_ofNat (k : ℕ) : value (ofNat k) = (k : ℚ≥0) := value_pair_zero k

/-- The acceptance criterion for the representation: comparison is primitive recursive. -/
theorem primrec_le : Primrec₂ le := by
  have h : PrimrecPred fun z : ℕ × ℕ ↦
      z.1.unpair.1 * (z.2.unpair.2 + 1) ≤ z.2.unpair.1 * (z.1.unpair.2 + 1) :=
    Primrec.nat_le.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))))
  exact primrecPred_iff_primrec_decide.mp h

theorem primrec_lt : Primrec₂ lt :=
  Primrec.not.comp (primrec_le.comp Primrec.snd Primrec.fst)

theorem primrec_ofNat : Primrec ofNat :=
  Primrec₂.natPair.comp Primrec.id (Primrec.const 0)

end NNRatCode
end AlgorithmicRandomness
