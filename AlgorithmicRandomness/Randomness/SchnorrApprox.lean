/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.FiniteOpen
import AlgorithmicRandomness.Randomness.Schnorr

/-!
# Exact finite-stage approximation for Schnorr tests

Gate 1 of the bridge from Schnorr randomness to computable randomness. The conditional
probability `μ (Uₙ ∩ [σ])` is only a computable real, but each *finite stage* of `Uₙ` meets
`[σ]` in a finite union of cylinders whose measure is an exact rational, and the Schnorr
modulus bounds the error.

The exact-rational conditioning machinery itself (`FiniteOpenCode.capWeight` and its coded
counterpart) lives in the coded finite-open layer, since trimming and this file both consume it.
What is Schnorr-specific, and all that remains here, is the pair of error bounds.

They are stated *additively* rather than with a difference, to avoid `ℝ≥0∞`
subtraction and to convert cleanly into a real absolute-error estimate later.
-/

open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## The two error bounds

Both are stated additively, so that no `ℝ≥0∞` subtraction ever appears. -/

/-- Stage error: at the modulus stage, the unenumerated part of `Uₙ` contributes at most `2⁻ᵏ`,
uniformly over the conditioning cylinder. -/
theorem stage_error (T : SchnorrTest) (n k : ℕ) (σ : BitString) :
    fairCoin (T.openCode.denote n ∩ cylinder σ)
      ≤ fairCoin (T.openCode.stageSet n (T.modulus.apply₂ n k) ∩ cylinder σ)
        + (2⁻¹ : ℝ≥0∞) ^ k := by
  have hsub : T.openCode.denote n ∩ cylinder σ
      ⊆ (T.openCode.stageSet n (T.modulus.apply₂ n k) ∩ cylinder σ)
        ∪ (T.openCode.denote n \ T.openCode.stageSet n (T.modulus.apply₂ n k)) := by
    rintro x ⟨hx, hxσ⟩
    by_cases hs : x ∈ T.openCode.stageSet n (T.modulus.apply₂ n k)
    · exact Or.inl ⟨hs, hxσ⟩
    · exact Or.inr ⟨hx, hs⟩
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  gcongr
  exact T.tail_le n k

/-- Truncation error: the level bounds sum geometrically past any cutoff. -/
theorem tail_error (T : SchnorrTest) (N : ℕ) (σ : BitString) :
    ∑' n : ℕ, fairCoin (T.openCode.denote (N + n) ∩ cylinder σ) ≤ (2⁻¹ : ℝ≥0∞) ^ N * 2 := by
  have hterm : ∀ n : ℕ, fairCoin (T.openCode.denote (N + n) ∩ cylinder σ)
      ≤ (2⁻¹ : ℝ≥0∞) ^ N * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    refine le_trans (measure_mono Set.inter_subset_left) ?_
    rw [← pow_add]
    exact T.measure_le (N + n)
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

end AlgorithmicRandomness
