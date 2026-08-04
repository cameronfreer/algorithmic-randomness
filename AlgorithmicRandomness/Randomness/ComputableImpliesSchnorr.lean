/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Randomness.SchnorrMartingale

/-!
# Computable randomness implies Schnorr randomness

Gate 3, closing the bridge. Given a Schnorr test capturing `x`, the conditional-probability
martingale of that test has unbounded capital along `x`, and Gate 2a's simulation transfers
that to a genuine `ComputableMartingale`.

The only substantive step is **synchronization**. Each level of the test contains a cylinder
around `x`, but at a different depth. `exists_initSeg_subset` produces a single initial segment
of `x` whose cylinder lies inside *all* of the first `N` levels at once, by induction on `N`:
the property is stated so that it persists automatically under further extension, which is what
lets the induction refine one more level without disturbing the ones already arranged.
-/

open MeasureTheory
open scoped NNRat NNReal ENNReal

namespace AlgorithmicRandomness

variable {T : SchnorrTest}

/-! ## Synchronization -/

/-- A single initial segment of `x` whose cylinder lies inside the first `N` levels at once. -/
theorem exists_initSeg_subset {x : Cantor} (hx : T.Captures x) (N : ℕ) :
    ∃ m, ∀ n < N, cylinder (initSeg x m) ⊆ T.openCode.denote n := by
  induction N with
  | zero => exact ⟨0, fun n hn ↦ absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨τ, hxτ, hτ⟩ := UniformOpenCode.exists_cylinder_subset_denote (hx N)
    refine ⟨max m τ.length, fun n hn ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | rfl
    · -- old levels survive, because a longer initial segment gives a smaller cylinder
      exact subset_trans (cylinder_anti (initSeg_prefix_of_le (le_max_left m τ.length)))
        (hm n hlt)
    · -- the new level, because the initial segment now extends its witness
      refine subset_trans (cylinder_anti ?_) hτ
      have hpre : initSeg x τ.length <+: initSeg x (max m τ.length) :=
        initSeg_prefix_of_le (le_max_right m τ.length)
      rwa [initSeg_of_mem_cylinder hxτ] at hpre

/-! ## Unbounded capital -/

/-- A level containing the whole cylinder contributes exactly `1`. -/
theorem levelMass_eq_one {n : ℕ} {σ : BitString} (h : cylinder σ ⊆ T.openCode.denote n) :
    levelMass T n σ = 1 := by
  rw [levelMass, Set.inter_eq_right.mpr h, fairCoin_cylinder]
  rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (by simp) (by simp)]

/-- If the first `N` levels all contain the cylinder, the capital there is at least `N`. -/
theorem le_schnorrMass_of_subset {σ : BitString} {N : ℕ}
    (h : ∀ n < N, cylinder σ ⊆ T.openCode.denote n) : (N : ℝ≥0∞) ≤ schnorrMass T σ := by
  refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (Finset.range N))
  rw [Finset.sum_congr rfl fun n hn ↦ levelMass_eq_one (h n (Finset.mem_range.mp hn))]
  simp

theorem le_schnorrCapital_of_subset {σ : BitString} {N : ℕ}
    (h : ∀ n < N, cylinder σ ⊆ T.openCode.denote n) : (N : ℝ≥0) ≤ schnorrCapital T σ := by
  rw [← ENNReal.coe_le_coe, coe_schnorrCapital]
  refine le_trans (le_of_eq ?_) (le_schnorrMass_of_subset h)
  simp

/-- The conditional-probability martingale of a capturing test has unbounded capital along the
captured point. -/
theorem exists_le_schnorrCapital {x : Cantor} (hx : T.Captures x) (N : ℕ) :
    ∃ m, (N : ℝ≥0) ≤ schnorrCapital T (initSeg x m) := by
  obtain ⟨m, hm⟩ := exists_initSeg_subset hx N
  exact ⟨m, le_schnorrCapital_of_subset hm⟩

/-! ## Transfer and the implication -/

/-- The simulation of the Schnorr martingale succeeds on any captured point. -/
theorem succeeds_simulate {x : Cantor} (hx : T.Captures x) :
    (schnorrApproximable T).simulate.Succeeds x := by
  intro c
  -- a natural above the requested rational threshold
  obtain ⟨N, hN⟩ := exists_nat_ge ((c : ℚ≥0) : ℝ)
  obtain ⟨m, hm⟩ := exists_le_schnorrCapital hx N
  refine ⟨m, ?_⟩
  have hcap : ((N : ℝ≥0) : ℝ) ≤ ((schnorrApproximable T).capital (initSeg x m) : ℝ) := by
    exact_mod_cast hm
  have hsim := ApproximableTreeMartingale.simulate_ge (D := schnorrApproximable T) (initSeg x m)
  have : ((c : ℚ≥0) : ℝ)
      ≤ (((schnorrApproximable T).simulate.capital (initSeg x m) : ℚ≥0) : ℝ) := by
    refine le_trans hN (le_trans ?_ hsim)
    simpa using hcap
  exact_mod_cast this

/-- **Computable randomness implies Schnorr randomness.** -/
theorem IsComputablyRandom.isSchnorrRandom {x : Cantor} (h : IsComputablyRandom x) :
    IsSchnorrRandom x := fun _ hT ↦ h _ (succeeds_simulate hT)

end AlgorithmicRandomness
