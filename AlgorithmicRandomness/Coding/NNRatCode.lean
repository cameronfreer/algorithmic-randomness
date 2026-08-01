/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Tactic.Positivity

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

end NNRatCode
end AlgorithmicRandomness
