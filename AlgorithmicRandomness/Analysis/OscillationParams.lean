/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.AffineDyadic

/-!
# The parameters of the oscillating construction

Only these parameters enter the program of BMN's oscillating martingale: the two grids, the two
thresholds, and the precision of the slope test. The analytic facts that select them — that both
grids carry cells of arbitrarily small width clearing the thresholds by the margin — are kept apart,
in `MonotoneOscillation`, so that the construction itself depends on no classical choice.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-- The executable data of the oscillating construction. -/
structure OscillationParams where
  /-- The grid whose cells the betting state uses. -/
  betGrid : AffineDyadicGrid
  /-- The grid whose cells the waiting state uses. -/
  waitGrid : AffineDyadicGrid
  /-- The lower threshold, as a coded nonnegative rational. -/
  betaCode : ℕ
  /-- The upper threshold. -/
  gammaCode : ℕ
  /-- The approximation precision of the slope test. -/
  precision : ℕ
  /-- The gap survives the approximation slack on both sides. Storing the robust form, rather than
  `β < γ`, is what later gives the multiplicative gain without reopening the selection. -/
  robustGap :
    (((NNRatCode.value betaCode : ℚ≥0) : ℝ) + (2⁻¹ : ℝ) ^ precision)
      < (((NNRatCode.value gammaCode : ℚ≥0) : ℝ) - (2⁻¹ : ℝ) ^ precision)

namespace OscillationParams

noncomputable def beta (P : OscillationParams) : ℝ :=
  ((NNRatCode.value P.betaCode : ℚ≥0) : ℝ)

noncomputable def gamma (P : OscillationParams) : ℝ :=
  ((NNRatCode.value P.gammaCode : ℚ≥0) : ℝ)

noncomputable def margin (P : OscillationParams) : ℝ := (2⁻¹ : ℝ) ^ P.precision

theorem margin_pos (P : OscillationParams) : 0 < P.margin := by
  rw [margin]
  positivity

theorem beta_add_margin_lt (P : OscillationParams) :
    P.beta + P.margin < P.gamma - P.margin := P.robustGap

theorem one_lt_ratio (P : OscillationParams) (hβ : 0 ≤ P.beta) :
    1 < (P.gamma - P.margin) / (P.beta + P.margin) := by
  have hpos : 0 < P.beta + P.margin := by linarith [P.margin_pos]
  rw [lt_div_iff₀ hpos]
  linarith [P.beta_add_margin_lt]

end OscillationParams

end AlgorithmicRandomness
