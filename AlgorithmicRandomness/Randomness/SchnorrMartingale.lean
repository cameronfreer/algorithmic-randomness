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

/-! ## The finite approximation

The schedule is frozen: level `n` is read at stage `modulus n (i + |σ| + n + 2)`, and levels
past `i + |σ| + 2` are dropped. The estimates are kept one-sided in `ℝ≥0∞`, so no subtraction
appears before the transport to `ℝ`. -/

/-- The stage at which level `n` is read. -/
def approxStage (T : SchnorrTest) (σ : BitString) (i n : ℕ) : ℕ :=
  T.modulus.apply₂ n (i + σ.length + n + 2)

/-- The mass of level `n` read at a finite stage. -/
noncomputable def stageMass (T : SchnorrTest) (n s : ℕ) (σ : BitString) : ℝ≥0∞ :=
  2 ^ σ.length * fairCoin (T.openCode.stageSet n s ∩ cylinder σ)

/-- The finite approximation to `schnorrMass` at precision `i`. -/
noncomputable def approxMass (T : SchnorrTest) (σ : BitString) (i : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range (i + σ.length + 2), stageMass T n (approxStage T σ i n) σ

theorem stageMass_le_levelMass (n s : ℕ) (σ : BitString) :
    stageMass T n s σ ≤ levelMass T n σ := by
  rw [stageMass, levelMass]
  gcongr
  exact UniformOpenCode.stageSet_subset_denote _ _ _

/-- One side of the estimate: the approximation never overshoots. -/
theorem approxMass_le (σ : BitString) (i : ℕ) : approxMass T σ i ≤ schnorrMass T σ := by
  refine le_trans (Finset.sum_le_sum fun n _ ↦ stageMass_le_levelMass n _ σ) ?_
  exact ENNReal.sum_le_tsum _

/-- The scaled per-level stage error, on the frozen schedule. -/
theorem levelMass_le_stageMass_add (σ : BitString) (i n : ℕ) :
    levelMass T n σ ≤ stageMass T n (approxStage T σ i n) σ
      + 2 ^ σ.length * (2⁻¹ : ℝ≥0∞) ^ (i + σ.length + n + 2) := by
  rw [levelMass, stageMass, approxStage, ← mul_add]
  gcongr
  exact stage_error T n (i + σ.length + n + 2) σ

/-- Geometric bookkeeping: `2^ℓ · 2⁻⁽ⁱ⁺ˡ⁺²⁾ · 2 = 2⁻⁽ⁱ⁺¹⁾`, the identity the frozen schedule is
chosen to make exact. Both the head and the tail estimate reduce to it. -/
theorem scale_identity (ℓ i : ℕ) :
    2 ^ ℓ * ((2⁻¹ : ℝ≥0∞) ^ (i + ℓ + 2) * 2) = (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by
  have hcancel : (2 : ℝ≥0∞) ^ ℓ * (2⁻¹ : ℝ≥0∞) ^ ℓ = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]
  have hinv : (2⁻¹ : ℝ≥0∞) * 2 = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
  have hsplit : (2⁻¹ : ℝ≥0∞) ^ (i + ℓ + 2)
      = (2⁻¹ : ℝ≥0∞) ^ (i + 1) * ((2⁻¹ : ℝ≥0∞) ^ ℓ * 2⁻¹) := by
    rw [show i + ℓ + 2 = (i + 1) + (ℓ + 1) by ring, pow_add, pow_succ (2⁻¹ : ℝ≥0∞) ℓ]
  rw [hsplit]
  calc (2 : ℝ≥0∞) ^ ℓ * ((2⁻¹ : ℝ≥0∞) ^ (i + 1) * ((2⁻¹ : ℝ≥0∞) ^ ℓ * 2⁻¹) * 2)
      = ((2 : ℝ≥0∞) ^ ℓ * (2⁻¹ : ℝ≥0∞) ^ ℓ) * ((2⁻¹ : ℝ≥0∞) * 2)
        * (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by ring
    _ = (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by rw [hcancel, hinv, one_mul, one_mul]

/-- The scaled head error sums to at most `2⁻⁽ⁱ⁺¹⁾`. -/
theorem head_error_le (σ : BitString) (i : ℕ) :
    ∑ n ∈ Finset.range (i + σ.length + 2),
      2 ^ σ.length * (2⁻¹ : ℝ≥0∞) ^ (i + σ.length + n + 2) ≤ (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by
  have hterm : ∀ n : ℕ, 2 ^ σ.length * (2⁻¹ : ℝ≥0∞) ^ (i + σ.length + n + 2)
      = (2 ^ σ.length * (2⁻¹ : ℝ≥0∞) ^ (i + σ.length + 2)) * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    rw [mul_assoc, ← pow_add]
    congr 2
    ring
  refine le_trans (Finset.sum_le_sum fun n _ ↦ le_of_eq (hterm n)) ?_
  refine le_trans (ENNReal.sum_le_tsum _) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, mul_assoc]
  exact le_of_eq (scale_identity σ.length i)

/-- The scaled tail past the cutoff is at most `2⁻⁽ⁱ⁺¹⁾`. -/
theorem tail_bound (σ : BitString) (i : ℕ) :
    ∑' n, levelMass T (n + (i + σ.length + 2)) σ ≤ (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by
  have hterm : ∀ n : ℕ, levelMass T (n + (i + σ.length + 2)) σ
      = 2 ^ σ.length * fairCoin (T.openCode.denote ((i + σ.length + 2) + n) ∩ cylinder σ) := by
    intro n; rw [levelMass, Nat.add_comm n (i + σ.length + 2)]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  refine le_trans ?_ (le_of_eq (scale_identity σ.length i))
  gcongr
  exact tail_error T (i + σ.length + 2) σ

/-- The complement tail is bounded by the shifted tail, via the surjection `m ↦ m + N`.
Kept private: the shift comparison has no other consumer. -/
private theorem tsum_compl_le_shift (σ : BitString) (N : ℕ) :
    ∑' n : ↥((Finset.range N : Finset ℕ) : Set ℕ)ᶜ, levelMass T (n : ℕ) σ
      ≤ ∑' m : ℕ, levelMass T (m + N) σ := by
  have hsurj : Function.Surjective
      (fun m : ℕ ↦ (⟨m + N, by simp⟩ : ↥((Finset.range N : Finset ℕ) : Set ℕ)ᶜ)) := by
    rintro ⟨n, hn⟩
    have hle : N ≤ n := by
      simp only [Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, not_lt] at hn
      exact hn
    exact ⟨n - N, by simp [Nat.sub_add_cancel hle]⟩
  exact ENNReal.tsum_le_tsum_comp_of_surjective hsurj fun n ↦ levelMass T (n : ℕ) σ

/-- The other side of the estimate: the approximation is short by at most `2⁻ⁱ`. -/
theorem schnorrMass_le_approxMass_add (σ : BitString) (i : ℕ) :
    schnorrMass T σ ≤ approxMass T σ i + (2⁻¹ : ℝ≥0∞) ^ i := by
  have hhead : ∑ n ∈ Finset.range (i + σ.length + 2), levelMass T n σ
      ≤ approxMass T σ i + (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by
    refine le_trans (Finset.sum_le_sum fun n _ ↦ levelMass_le_stageMass_add σ i n) ?_
    rw [Finset.sum_add_distrib, approxMass]
    gcongr
    exact head_error_le σ i
  have htail : ∑' n : ↥((Finset.range (i + σ.length + 2) : Finset ℕ) : Set ℕ)ᶜ,
      levelMass T (n : ℕ) σ ≤ (2⁻¹ : ℝ≥0∞) ^ (i + 1) :=
    le_trans (tsum_compl_le_shift σ (i + σ.length + 2)) (tail_bound σ i)
  calc schnorrMass T σ
      = ∑ n ∈ Finset.range (i + σ.length + 2), levelMass T n σ
        + ∑' n : ↥((Finset.range (i + σ.length + 2) : Finset ℕ) : Set ℕ)ᶜ,
            levelMass T (n : ℕ) σ :=
        (ENNReal.sum_add_tsum_compl _ _).symm
    _ ≤ (approxMass T σ i + (2⁻¹ : ℝ≥0∞) ^ (i + 1)) + (2⁻¹ : ℝ≥0∞) ^ (i + 1) :=
        add_le_add hhead htail
    _ = approxMass T σ i + (2⁻¹ : ℝ≥0∞) ^ i := by
        have hhalf : (2⁻¹ : ℝ≥0∞) ^ (i + 1) + (2⁻¹ : ℝ≥0∞) ^ (i + 1) = (2⁻¹ : ℝ≥0∞) ^ i := by
          rw [← two_mul, pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) ((2⁻¹ : ℝ≥0∞) ^ i),
            mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
        rw [add_assoc, hhalf]

/-! ## The coded approximation

The exact bridge theorem `coe_value_approxCode` below is the only place the computation meets
the measure theory; once it is available the two `ℝ≥0∞` estimates transport without ever
unfolding the computation again. -/

open Nat.Partrec (Code)

/-- Distributing the `ℚ≥0 → ℝ≥0∞` cast over a power-of-two scaling. -/
private theorem coe_nnrat_mul_pow (q : ℚ≥0) (k : ℕ) :
    ((q * 2 ^ k : ℚ≥0) : ℝ≥0∞) = (q : ℝ≥0∞) * 2 ^ k := by
  rw [← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast]
  push_cast
  rfl

/-- Distributing the `ℚ≥0 → ℝ≥0∞` cast over addition. -/
private theorem coe_nnrat_add (a b : ℚ≥0) : ((a + b : ℚ≥0) : ℝ≥0∞) = (a : ℝ≥0∞) + b := by
  rw [← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast]
  push_cast
  rfl

private theorem coe_nnrat_zero : ((0 : ℚ≥0) : ℝ≥0∞) = 0 := by
  rw [← ENNReal.coe_nnratCast]
  push_cast
  rfl

/-- The coded contribution of level `n`: the exact rational measure of the scheduled stage,
conditioned on `σ` and scaled by the cylinder factor. -/
def levelCode (T : SchnorrTest) (σ : BitString) (i n : ℕ) : ℕ :=
  NNRatCode.scalePowTwo σ.length
    (FiniteOpenCode.capWeightCode
      (stringStageList T.openCode.program n (approxStage T σ i n)) σ)

theorem coe_value_levelCode (σ : BitString) (i n : ℕ) :
    ((NNRatCode.value (levelCode T σ i n) : ℚ≥0) : ℝ≥0∞)
      = stageMass T n (approxStage T σ i n) σ := by
  rw [levelCode, NNRatCode.value_scalePowTwo, stageMass, UniformOpenCode.stageSet,
    UniformOpenCode.stage, ← stringStageList_toFinset,
    FiniteOpenCode.fairCoin_cylinderUnion_inter_cylinder,
    FiniteOpenCode.value_capWeightCode, mul_comm ((2 : ℚ≥0) ^ σ.length) _,
    coe_nnrat_mul_pow, mul_comm]

/-- The coded partial sum of the first `N` levels. -/
def approxCodeUpTo (T : SchnorrTest) (σ : BitString) (i : ℕ) : ℕ → ℕ
  | 0 => Nat.pair 0 0
  | N + 1 => NNRatCode.add (approxCodeUpTo T σ i N) (levelCode T σ i N)

theorem coe_value_approxCodeUpTo (σ : BitString) (i N : ℕ) :
    ((NNRatCode.value (approxCodeUpTo T σ i N) : ℚ≥0) : ℝ≥0∞)
      = ∑ n ∈ Finset.range N, stageMass T n (approxStage T σ i n) σ := by
  induction N with
  | zero => rw [approxCodeUpTo, NNRatCode.value_pair_zero, Nat.cast_zero,
      coe_nnrat_zero, Finset.range_zero, Finset.sum_empty]
  | succ N ih =>
    rw [approxCodeUpTo, NNRatCode.value_add, coe_nnrat_add, Finset.sum_range_succ, ih,
      coe_value_levelCode σ i N]

/-- The coded approximation to `schnorrMass` at precision `i`. -/
def approxCode (T : SchnorrTest) (σ : BitString) (i : ℕ) : ℕ :=
  approxCodeUpTo T σ i (i + σ.length + 2)

/-- **The exact bridge**: the coded computation denotes exactly the semantic approximation. -/
theorem coe_value_approxCode (σ : BitString) (i : ℕ) :
    ((NNRatCode.value (approxCode T σ i) : ℚ≥0) : ℝ≥0∞) = approxMass T σ i :=
  coe_value_approxCodeUpTo σ i _

end AlgorithmicRandomness
