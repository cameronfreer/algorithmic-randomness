/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Martingale.Simulate
import AlgorithmicRandomness.Randomness.SchnorrApprox

/-!
# The conditional-probability martingale of a Schnorr test

Internal Gate 2b of the bridge from Schnorr randomness to computable randomness. Level `n`
contributes `2^|σ| · μ (Uₙ ∩ [σ])`, and the total capital is the sum over levels. Each level is
exactly a tree martingale, because the two child cylinders partition the parent.

The level sum is taken in `ℝ≥0∞`, where `tsum` is unconditionally additive and commutes with
scalars with no summability side conditions, and the martingale itself is `ℝ≥0`-valued. The
single fact bridging the two is `schnorrMass_ne_top`, proved once from the geometric bound
before any conversion happens.
-/

open MeasureTheory
open scoped NNRat NNReal ENNReal

namespace AlgorithmicRandomness

variable (T : SchnorrTest)

/-! ## The mass contributed by one level -/

/-- The mass level `n` contributes at `σ`: the conditional measure scaled by the cylinder size. -/
noncomputable def levelMass (n : ℕ) (σ : BitString) : ℝ≥0∞ :=
  2 ^ σ.length * fairCoin (T.openCode.denote n ∩ cylinder σ)

variable {T}

theorem levelMass_le (n : ℕ) (σ : BitString) :
    levelMass T n σ ≤ 2 ^ σ.length * (2⁻¹ : ℝ≥0∞) ^ n := by
  rw [levelMass]
  gcongr
  exact le_trans (measure_mono Set.inter_subset_left) (T.measure_le n)

/-- Each level is exactly a tree martingale: the two child cylinders partition the parent. -/
theorem levelMass_fair (n : ℕ) (σ : BitString) :
    levelMass T n (σ ++ [false]) + levelMass T n (σ ++ [true]) = 2 * levelMass T n σ := by
  have hdisj : Disjoint (T.openCode.denote n ∩ cylinder (σ ++ [false]))
      (T.openCode.denote n ∩ cylinder (σ ++ [true])) := by
    refine Disjoint.inter_left' _ (Disjoint.inter_right' _ (disjoint_cylinder_iff.mpr ?_))
    rintro (h | h) <;> exact absurd (h.eq_of_length (by simp)) (by simp)
  have hmeas : MeasurableSet (T.openCode.denote n ∩ cylinder (σ ++ [true])) :=
    (UniformOpenCode.measurableSet_denote _ _).inter (measurableSet_cylinder _)
  have hsplit : fairCoin (T.openCode.denote n ∩ cylinder (σ ++ [false]))
      + fairCoin (T.openCode.denote n ∩ cylinder (σ ++ [true]))
      = fairCoin (T.openCode.denote n ∩ cylinder σ) := by
    rw [← measure_union hdisj hmeas, ← Set.inter_union_distrib_left, ← cylinder_eq_union_concat]
  rw [levelMass, levelMass, levelMass, List.length_append, List.length_append]
  simp only [List.length_singleton, pow_succ]
  rw [← mul_add, hsplit]
  ring

/-! ## The total mass, and its finiteness -/

/-- The total mass at `σ`, summed in `ℝ≥0∞` so that no summability side condition arises. -/
noncomputable def schnorrMass (T : SchnorrTest) (σ : BitString) : ℝ≥0∞ :=
  ∑' n, levelMass T n σ

/-- The geometric bound: the levels sum to at most twice the cylinder scale. -/
theorem schnorrMass_le (σ : BitString) : schnorrMass T σ ≤ 2 ^ σ.length * 2 := by
  refine le_trans (ENNReal.tsum_le_tsum fun n ↦ levelMass_le n σ) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

/-- The single fact bridging `ℝ≥0∞` summation and the `ℝ≥0`-valued martingale. -/
theorem schnorrMass_ne_top (σ : BitString) : schnorrMass T σ ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (schnorrMass_le σ)
  exact ENNReal.mul_ne_top (by simp) (by simp)

theorem schnorrMass_fair (σ : BitString) :
    schnorrMass T (σ ++ [false]) + schnorrMass T (σ ++ [true]) = 2 * schnorrMass T σ := by
  rw [schnorrMass, schnorrMass, schnorrMass, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n ↦ levelMass_fair n σ

/-! ## The martingale -/

/-- The conditional-probability martingale of a Schnorr test. -/
noncomputable def schnorrCapital (T : SchnorrTest) (σ : BitString) : ℝ≥0 :=
  (schnorrMass T σ).toNNReal

theorem coe_schnorrCapital (σ : BitString) :
    ((schnorrCapital T σ : ℝ≥0) : ℝ≥0∞) = schnorrMass T σ :=
  ENNReal.coe_toNNReal (schnorrMass_ne_top σ)

theorem schnorrCapital_fair (σ : BitString) :
    schnorrCapital T (σ ++ [false]) + schnorrCapital T (σ ++ [true]) = 2 * schnorrCapital T σ := by
  rw [← ENNReal.coe_inj]
  push_cast [coe_schnorrCapital]
  exact schnorrMass_fair σ

/-- The semantic martingale attached to a Schnorr test. -/
noncomputable def schnorrMartingale (T : SchnorrTest) : RealTreeMartingale where
  capital := schnorrCapital T
  fair := schnorrCapital_fair

@[simp] theorem schnorrMartingale_capital (σ : BitString) :
    (schnorrMartingale T).capital σ = schnorrCapital T σ := rfl

end AlgorithmicRandomness
