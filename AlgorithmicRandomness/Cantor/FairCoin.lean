/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

/-!
# Fair-coin measure on Cantor space

`fairCoin` is the countable product over `ℕ` of the uniform probability measure `fairBit` on
`Bool`, constructed with mathlib's `MeasureTheory.Measure.infinitePi`. The key computation is
`fairCoin_cylinder`: the cylinder on a string `σ` has measure `2⁻¹ ^ σ.length`, exactly.
-/

open MeasureTheory

namespace AlgorithmicRandomness

/-- The uniform probability measure on `Bool`. -/
noncomputable def fairBit : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure fairBit := PMF.toMeasure.isProbabilityMeasure _

@[simp]
theorem fairBit_singleton (b : Bool) : fairBit {b} = 2⁻¹ := by
  rw [fairBit, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.uniformOfFintype_apply]
  simp

/-- The fair-coin measure on Cantor space: the countable product over `ℕ` of the uniform
probability measure on `Bool`. -/
noncomputable def fairCoin : Measure Cantor := Measure.infinitePi fun _ ↦ fairBit

instance : IsProbabilityMeasure fairCoin :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ ↦ fairBit))

/-- The cylinder on a string `σ` has fair-coin measure exactly `2⁻¹ ^ σ.length`. -/
theorem fairCoin_cylinder (σ : BitString) : fairCoin (cylinder σ) = 2⁻¹ ^ σ.length := by
  rw [cylinder_eq_measureTheory_cylinder, fairCoin,
    Measure.infinitePi_cylinder (μ := fun _ : ℕ ↦ fairBit) (measurableSet_singleton _),
    ← Set.univ_pi_singleton (BitString.rangeRestriction σ), Measure.pi_pi]
  simp

theorem fairCoin_cylinder_pos (σ : BitString) : 0 < fairCoin (cylinder σ) := by
  rw [fairCoin_cylinder]
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by simp)) _

end AlgorithmicRandomness
