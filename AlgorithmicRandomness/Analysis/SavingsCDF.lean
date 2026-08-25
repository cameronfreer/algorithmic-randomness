/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.ComputableMonotone
import AlgorithmicRandomness.Martingale.Savings
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Effective atomlessness from savings

A martingale with savings gains at most one unit per bit, so the mass it assigns to a level-`n`
cell is at most `2⁻ⁿ (M ∅ + n)`. That quantity tends to zero, which is the effective atomlessness
modulus: it bounds, uniformly in the cell, how much mass a single cell can carry, and hence how far
the cumulative function can move across one.

The boundary between exact and approximate is drawn here. The *search* for a level fine enough for
a requested precision is a comparison of coded rationals and stays in `ℚ≥0`; only its *termination*
is proved in `ℝ`, where the pinned mathlib supplies the linear-versus-geometric decay
`tendsto_self_mul_const_pow_of_lt_one`. Rebuilding that decay over `ℚ≥0` would be work with no
payoff, since the certificate is never executed.
-/

open scoped NNRat

open Filter

namespace AlgorithmicRandomness

variable {M : TreeMartingale}

/-- The uniform bound on the mass of a level-`n` cell. -/
def cellBound (M : TreeMartingale) (n : ℕ) : ℚ≥0 :=
  (2⁻¹ : ℚ≥0) ^ n * (M.capital [] + n)

/-- **The effective cell estimate.** With savings, no cell of level `n` carries more mass than
`cellBound M n`, whatever the string. -/
theorem cellMass_le (hs : M.SavingsProperty) (σ : BitString) :
    (2⁻¹ : ℚ≥0) ^ σ.length * M.capital σ ≤ cellBound M σ.length :=
  mul_le_mul_of_nonneg_left (hs.capital_le_root_add_length σ) zero_le

/-- The termination certificate, in `ℝ`: a constant times a geometric sequence plus a linear one. -/
private theorem tendsto_coe_cellBound_zero (M : TreeMartingale) :
    Tendsto (fun n ↦ ((cellBound M n : ℚ≥0) : ℝ)) atTop (nhds 0) := by
  have hgeom : Tendsto (fun n : ℕ ↦ ((M.capital [] : ℚ≥0) : ℝ) * (2⁻¹ : ℝ) ^ n) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)
    simpa using h.const_mul (((M.capital [] : ℚ≥0) : ℝ))
  have hlin : Tendsto (fun n : ℕ ↦ (n : ℝ) * (2⁻¹ : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hsum := hgeom.add hlin
  rw [add_zero] at hsum
  refine hsum.congr fun n ↦ ?_
  rw [cellBound]
  push_cast
  ring

/-- **The selector's contract.** Some level is fine enough for any requested precision. The search
itself is a comparison of coded rationals; only this proof passes through the reals. -/
theorem exists_cellBound_le (M : TreeMartingale) (k : ℕ) :
    ∃ n, cellBound M n ≤ (2⁻¹ : ℚ≥0) ^ k := by
  have hpos : (0 : ℝ) < ((2⁻¹ : ℚ≥0) ^ k : ℚ≥0) := by positivity
  have hev := (tendsto_coe_cellBound_zero M).eventually (gt_mem_nhds hpos)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, le_of_lt (by exact_mod_cast hn)⟩

end AlgorithmicRandomness
