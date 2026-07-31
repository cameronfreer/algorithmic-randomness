/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.EffectiveOpen.Reindex

/-!
# Martin-Löf tests and Martin-Löf randomness

A `MartinLofTest` is a coded uniformly c.e. family of open sets carrying the semantic bound
`μ (Uₙ) ≤ 2⁻ⁿ`. Nestedness is deliberately **not** required: it is a normal form to be proved
later, not part of the definition.

The main results are that each test's capture set `⋂ n, Uₙ` is measurable and null
(`fairCoin_captureSet`), and the derived exact finite-stage bound `stageWeight_le`, which is
the rational-valued form that later trimming constructions compare against.

The acceptance example `replicateTrueTest` captures the constant-`true` point, giving the
library's first non-randomness result: `¬IsMartinLofRandom (fun _ ↦ true)`.

Universal tests, trimming, global conullity, and Schnorr machinery are out of scope here.
-/

open MeasureTheory
open scoped NNRat NNReal ENNReal

namespace AlgorithmicRandomness

/-- A Martin-Löf test: a coded uniformly c.e. family of open sets with the semantic measure
bound `μ (Uₙ) ≤ 2⁻ⁿ`. Nestedness is not required. -/
structure MartinLofTest where
  /-- The coded uniformly c.e. family of open sets. -/
  openCode : UniformOpenCode
  /-- The defining measure bound on the `n`-th open set. -/
  measure_le : ∀ n, fairCoin (openCode.denote n) ≤ 2⁻¹ ^ n

namespace MartinLofTest

/-- The set of points captured by a test: those lying in every level. -/
def captureSet (T : MartinLofTest) : Set Cantor := ⋂ n, T.openCode.denote n

/-- `T` captures `x` when `x` lies in every level of `T`. -/
def Captures (T : MartinLofTest) (x : Cantor) : Prop := ∀ n, x ∈ T.openCode.denote n

@[simp]
theorem mem_captureSet {T : MartinLofTest} {x : Cantor} : x ∈ T.captureSet ↔ T.Captures x := by
  simp [captureSet, Captures]

theorem measurableSet_captureSet (T : MartinLofTest) : MeasurableSet T.captureSet :=
  MeasurableSet.iInter fun n ↦ UniformOpenCode.measurableSet_denote T.openCode n

/-- Every individual Martin-Löf test captures a null set. -/
theorem fairCoin_captureSet (T : MartinLofTest) : fairCoin T.captureSet = 0 := by
  refine ENNReal.eq_zero_of_le_mul_pow (ε := 1) (r := 2⁻¹)
    (ENNReal.inv_lt_one.mpr (by norm_num)) fun n ↦ ?_
  refine le_trans (measure_mono (Set.iInter_subset _ n)) ?_
  simpa using T.measure_le n

/-! ## Randomness -/

end MartinLofTest

/-- A point is Martin-Löf random when no Martin-Löf test captures it. -/
def IsMartinLofRandom (x : Cantor) : Prop := ∀ T : MartinLofTest, ¬T.Captures x

theorem isMartinLofRandom_iff_not_mem_captureSet {x : Cantor} :
    IsMartinLofRandom x ↔ ∀ T : MartinLofTest, x ∉ T.captureSet := by
  simp [IsMartinLofRandom]

theorem not_isMartinLofRandom_of_captures {T : MartinLofTest} {x : Cantor}
    (h : T.Captures x) : ¬IsMartinLofRandom x := fun hx ↦ hx T h

namespace MartinLofTest

/-! ## Exact finite-stage bounds -/

theorem coe_stageWeight_le (T : MartinLofTest) (n s : ℕ) :
    ((T.openCode.stageWeight n s : ℝ≥0) : ℝ≥0∞) ≤ 2⁻¹ ^ n :=
  (UniformOpenCode.fairCoin_denote_le_iff _ _ _).mp (T.measure_le n) s

/-- The exact rational form of the test bound: every finite stage of `Uₙ` has weight at most
`2⁻ⁿ`. This is the comparison later trimming constructions perform in `ℚ≥0`. -/
theorem stageWeight_le (T : MartinLofTest) (n s : ℕ) :
    T.openCode.stageWeight n s ≤ (2⁻¹ : ℚ≥0) ^ n := by
  have h := coe_stageWeight_le T n s
  rw [show (2⁻¹ : ℝ≥0∞) ^ n = ((((2⁻¹ : ℚ≥0) ^ n : ℚ≥0) : ℝ≥0) : ℝ≥0∞) by push_cast; rfl,
    ENNReal.coe_le_coe] at h
  exact_mod_cast h

/-! ## Shifts -/

/-- Shifting a test by a fixed offset is again a test: level `n` becomes level `n + m`, whose
bound `2⁻⁽ⁿ⁺ᵐ⁾` is at most `2⁻ⁿ`. -/
def shift (T : MartinLofTest) (m : ℕ) : MartinLofTest where
  openCode := T.openCode.shift m
  measure_le n := by
    rw [UniformOpenCode.denote_shift]
    refine (T.measure_le (n + m)).trans ?_
    rw [pow_add]
    exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (by simp))

@[simp]
theorem shift_openCode (T : MartinLofTest) (m : ℕ) :
    (T.shift m).openCode = T.openCode.shift m := rfl

/-- A captured point stays captured after shifting. The converse needs nestedness, which is
not assumed. -/
theorem captures_shift_of_captures {T : MartinLofTest} {x : Cantor} (h : T.Captures x)
    (m : ℕ) : (T.shift m).Captures x := by
  intro n
  rw [Captures] at h
  rw [shift_openCode, UniformOpenCode.denote_shift]
  exact h (n + m)

/-! ## Acceptance example -/

/-- The test built from the prefix cylinders of the constant-`true` point: level `n` is
`[true^n]`, of measure exactly `2⁻ⁿ`. -/
def replicateTrueTest : MartinLofTest where
  openCode := UniformOpenCode.replicateTrueOpen
  measure_le n := le_of_eq (UniformOpenCode.fairCoin_denote_replicateTrueOpen n)

@[simp]
theorem replicateTrueTest_openCode :
    replicateTrueTest.openCode = UniformOpenCode.replicateTrueOpen := rfl

theorem captures_replicateTrueTest : replicateTrueTest.Captures (fun _ ↦ true) := fun n ↦ by
  rw [replicateTrueTest_openCode, UniformOpenCode.denote_replicateTrueOpen]
  intro i
  simp

end MartinLofTest

/-- The constant-`true` sequence is not Martin-Löf random. -/
theorem not_isMartinLofRandom_const_true : ¬IsMartinLofRandom (fun _ ↦ true) :=
  not_isMartinLofRandom_of_captures MartinLofTest.captures_replicateTrueTest

end AlgorithmicRandomness
