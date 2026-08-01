/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.NNRatCode
import AlgorithmicRandomness.Coding.TotalCode
import AlgorithmicRandomness.Martingale.Ville

/-!
# Computable martingales and computable randomness

A `ComputableMartingale` is a tree martingale together with an actual program computing its
capital in the coded rational representation, plus the correctness bridge — the same shape as
`ComputableCantorPoint` and `NatFunctionCode`.

The capital is transmitted as a `NNRatCode`, never as an `Encodable ℚ≥0` value, so that later
phases can run a primitive recursive threshold test (`NNRatCode.primrec_le`) inside a program
and turn rational threshold crossings into coded c.e. opens.

Success is unbounded rational capital. The acceptance example `betOnTrue` doubles on `true` and
busts on `false`, succeeding on the constant-`true` point.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-- A tree martingale with a program computing its capital in the coded rational
representation, and the evaluation witness. -/
structure ComputableMartingale extends TreeMartingale where
  /-- The program, outputting a coded nonnegative rational on the code of a string. -/
  program : NatFunctionCode
  /-- The correctness bridge. -/
  eval_capital : ∀ σ, NNRatCode.value (program.toFun (Encodable.encode σ)) = capital σ

/-- A martingale succeeds on `x` when its capital along `x` is unbounded. -/
def TreeMartingale.Succeeds (d : TreeMartingale) (x : Cantor) : Prop :=
  ∀ c : ℚ≥0, ∃ n, c ≤ d.capital (initSeg x n)

/-- A point is computably random when no computable martingale succeeds on it. -/
def IsComputablyRandom (x : Cantor) : Prop := ∀ d : ComputableMartingale, ¬d.Succeeds x

theorem not_isComputablyRandom_of_succeeds {d : ComputableMartingale} {x : Cantor}
    (h : d.Succeeds x) : ¬IsComputablyRandom x := fun hx ↦ hx d h

/-! ## The acceptance example: betting everything on `true` -/

/-- All bits of `σ` are `true`, phrased by index lookup so it is primitive recursive. -/
def allTrue (σ : BitString) : Bool := decide (List.idxOf false σ = σ.length)

theorem allTrue_iff (σ : BitString) : allTrue σ = true ↔ false ∉ σ := by
  rw [allTrue, decide_eq_true_iff, ← List.idxOf_lt_length_iff (a := false) (l := σ), not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm (List.idxOf_le_length) h⟩

@[simp] theorem allTrue_append_false (σ : BitString) : allTrue (σ ++ [false]) = false := by
  rw [Bool.eq_false_iff, ne_eq, allTrue_iff]
  simp

@[simp] theorem allTrue_append_true (σ : BitString) : allTrue (σ ++ [true]) = allTrue σ := by
  rcases h : allTrue σ with _ | _
  · rw [Bool.eq_false_iff, ne_eq, allTrue_iff]
    rw [Bool.eq_false_iff, ne_eq, allTrue_iff, not_not] at h
    simpa using h
  · rw [allTrue_iff] at h ⊢
    simpa using h

/-- Capital `2 ^ |σ|` while `σ` is all `true`, and `0` once a `false` appears. -/
def betOnTrueCapital (σ : BitString) : ℚ≥0 :=
  if allTrue σ then 2 ^ σ.length else 0

theorem betOnTrueCapital_fair (σ : BitString) :
    betOnTrueCapital (σ ++ [false]) + betOnTrueCapital (σ ++ [true]) = 2 * betOnTrueCapital σ := by
  rcases h : allTrue σ with _ | _
  · simp [betOnTrueCapital, h]
  · simp [betOnTrueCapital, h, pow_succ, mul_comm]

/-- The coded capital: numerator `2 ^ |σ|` or `0`, denominator `1`. -/
def betOnTrueCode (m : ℕ) : ℕ :=
  Nat.pair (((Encodable.decode m : Option BitString).map fun σ ↦
    if allTrue σ = true then 2 ^ σ.length else 0).getD 0) 0

theorem computable_betOnTrueCode : Computable betOnTrueCode := by
  have hall : Primrec allTrue :=
    primrecPred_iff_primrec_decide.mp
      (Primrec.eq.comp (Primrec.list_idxOf.comp (Primrec.const false) Primrec.id)
        Primrec.list_length)
  have hbody : Primrec fun σ : BitString ↦ if allTrue σ = true then 2 ^ σ.length else 0 :=
    Primrec.ite (Primrec.eq.comp hall (Primrec.const true))
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.list_length)
      (Primrec.const 0)
  exact (Primrec₂.natPair.comp
    (Primrec.option_getD.comp ((Primrec.option_map₁ hbody).comp Primrec.decode)
      (Primrec.const 0))
    (Primrec.const 0)).to_comp

/-- The martingale that bets everything on `true`, as a coded object. -/
noncomputable def betOnTrue : ComputableMartingale where
  capital := betOnTrueCapital
  fair := betOnTrueCapital_fair
  program := NatFunctionCode.ofComputable computable_betOnTrueCode
  eval_capital σ := by
    rw [NatFunctionCode.ofComputable_toFun, betOnTrueCode, Encodable.encodek]
    simp only [Option.map_some, Option.getD_some]
    rw [NNRatCode.value_pair_zero, betOnTrueCapital]
    split <;> simp

@[simp]
theorem betOnTrue_capital (σ : BitString) : betOnTrue.capital σ = betOnTrueCapital σ := rfl

theorem betOnTrue_succeeds : betOnTrue.Succeeds (fun _ ↦ true) := by
  intro c
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R := ℚ≥0) c (by norm_num : (1 : ℚ≥0) < 2)
  refine ⟨n, hn.le.trans (le_of_eq ?_)⟩
  have hall : allTrue (initSeg (fun _ ↦ true) n) = true := by
    rw [allTrue_iff]
    simp [initSeg]
  rw [betOnTrue_capital, betOnTrueCapital, if_pos hall, length_initSeg]

theorem not_isComputablyRandom_const_true : ¬IsComputablyRandom (fun _ ↦ true) :=
  not_isComputablyRandom_of_succeeds betOnTrue_succeeds

end AlgorithmicRandomness
