/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.BinaryExpansion
import AlgorithmicRandomness.Analysis.CDFProgram
import AlgorithmicRandomness.Analysis.ChordSlope
import AlgorithmicRandomness.Martingale.Oscillation

/-!
# Failure of computable randomness produces a nondifferentiability point

This file is composition only; every mathematical ingredient was proved elsewhere.

The chain: a point that is not computably random admits a computable martingale succeeding on it
(`IsComputablyRandom`); `withSavings` normalizes it; `oscillator` converts the normalized
martingale into one whose capital stays in `[1, 4]` and hits exactly `3` and exactly `2`
arbitrarily late along that path; `toComputableLipschitz` turns *that* into a computable Lipschitz
function whose chord slope across the prefix interval `[σ]` is exactly the capital at `σ`; and
`realOf x` sits inside every prefix interval, whose widths shrink. Two frequently attained
distinct chord slopes then refute differentiability there.

The one seam worth naming is `prefixChordSlope_toComputableLipschitz`. `cdf_slope` already says
the chord slope across `[σ]` *is* the capital at `σ`, exactly and with no error term — that was
the point of building the cumulative function at dyadic endpoints directly rather than through a
measure. What this file adds is only that the packaged `toFun` agrees with `cdfLeft`/`cdfRight` at
those endpoints, which it does by way of the grid.

## Scope

This is the reverse direction of Freer–Kjos-Hanssen–Nies–Stephan (arXiv:1402.2429, Theorem 4.2),
in *sequence* form: the hypothesis is about a point of Cantor space and the conclusion is about
`realOf` of it. Two things are deliberately not claimed.

The paper's real-number formulation additionally needs a randomness predicate on reals and a
bridge in the other direction — that every `z ∈ [0, 1]` is `realOf` of some sequence. Neither is
here.

The published theorem is a biconditional, and the forward direction is not here and is not close.
It reduces a computable Lipschitz `f` to the nondecreasing `g x = f x + c * x` and then invokes
the Brattka–Miller–Nies characterization of computable randomness by differentiability of
computable nondecreasing functions (arXiv:1104.4465). That is a substantial effective-analysis
development, not a wrapper.

Finally, "computable Lipschitz function" here means `ComputableLipschitz`: exact rational values
at the dyadic cut points plus a natural Lipschitz bound. That is a choice of presentation, and
statements below should be read against it.
-/

open Filter Topology

namespace AlgorithmicRandomness

/-! ## The prefix chord slopes -/

/-- The slope of the chord across the `n`-th prefix interval of `x`. -/
noncomputable def prefixChordSlope (f : ℝ → ℝ) (x : Cantor) (n : ℕ) : ℝ :=
  slope f (dyadicLeft (initSeg x n)) (dyadicRight (initSeg x n))

/-- The packaged function agrees with the cumulative function at a left endpoint. -/
theorem toComputableLipschitz_toFun_dyadicLeft (M : ComputableMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) (σ : BitString) :
    (M.toComputableLipschitz hK).toFun (dyadicLeft σ) = cdfLeft M.toTreeMartingale σ := by
  rw [dyadicLeft_eq_gridPoint, toComputableLipschitz_toFun_gridPoint M hK
      (gridIndex_lt_two_pow σ).le,
    dyadicCDF_eq_gridCDF, cdfLeft_eq_gridCDF]

/-- And at a right endpoint. -/
theorem toComputableLipschitz_toFun_dyadicRight (M : ComputableMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) (σ : BitString) :
    (M.toComputableLipschitz hK).toFun (dyadicRight σ) = cdfRight M.toTreeMartingale σ := by
  rw [dyadicRight_eq_gridPoint_succ, toComputableLipschitz_toFun_gridPoint M hK
      (gridIndex_lt_two_pow σ),
    dyadicCDF_eq_gridCDF, cdfRight_eq_gridCDF]

/-- **The seam.** The chord slope across the `n`-th prefix interval is the capital there, exactly.
-/
theorem prefixChordSlope_toComputableLipschitz (M : ComputableMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) (x : Cantor) (n : ℕ) :
    prefixChordSlope (M.toComputableLipschitz hK).toFun x n
      = ((M.capital (initSeg x n) : ℚ≥0) : ℝ) := by
  rw [prefixChordSlope, slope_def_field, toComputableLipschitz_toFun_dyadicLeft,
    toComputableLipschitz_toFun_dyadicRight, cdf_slope]

/-! ## Nonconvergence along a path where the source succeeds -/

/-- The oscillator's chord slopes take the values `3` and `2` arbitrarily late, hence do not
converge. -/
theorem not_exists_tendsto_prefixChordSlope_oscillator (S : SavingsComputableMartingale)
    {x : Cantor} (hx : S.toTreeMartingale.Succeeds x)
    (h4 : ∀ σ, S.oscillator.capital σ ≤ (4 : ℚ≥0)) :
    ¬ ∃ L, Tendsto (prefixChordSlope
      (S.oscillator.toComputableLipschitz h4).toFun x) atTop (𝓝 L) := by
  refine not_exists_tendsto_of_frequently_eq (p := (3 : ℝ)) (q := (2 : ℝ)) (by norm_num) ?_ ?_
  · refine (SavingsComputableMartingale.frequently_oscillator_capital_eq_three hx).mono
      fun n hn ↦ ?_
    rw [prefixChordSlope_toComputableLipschitz, hn]
    norm_num
  · refine (SavingsComputableMartingale.frequently_oscillator_capital_eq_two hx).mono
      fun n hn ↦ ?_
    rw [prefixChordSlope_toComputableLipschitz, hn]
    norm_num

/-! ## The theorem -/

/-- A computable martingale succeeding on `x` yields a computable Lipschitz function that is not
differentiable at `realOf x`. -/
theorem exists_computableLipschitz_not_differentiableAt_of_succeeds {d : ComputableMartingale}
    {x : Cantor} (hd : d.Succeeds x) :
    ∃ f : ComputableLipschitz, ¬DifferentiableAt ℝ f.toFun (realOf x) := by
  set S := d.withSavings with hS
  have hSx : S.toTreeMartingale.Succeeds x := d.succeeds_withSavings hd
  have h4 : ∀ σ, S.oscillator.capital σ ≤ (4 : ℚ≥0) := fun σ ↦ (S.oscillator_bounds σ).2
  refine ⟨S.oscillator.toComputableLipschitz h4, ?_⟩
  refine not_differentiableAt_of_not_tendsto_chordSlope
    (a := fun n ↦ dyadicLeft (initSeg x n)) (b := fun n ↦ dyadicRight (initSeg x n))
    (fun n ↦ realOf_mem_dyadicInterval x n)
    (fun n ↦ dyadicLeft_lt_dyadicRight _) ?_
    (not_exists_tendsto_prefixChordSlope_oscillator S hSx h4)
  simpa [dyadicRight] using tendsto_prefix_width_zero x

/-- **The reverse direction of the Lipschitz characterization, in sequence form.** If `x` is not
computably random then some computable Lipschitz function fails to be differentiable at the real
`x` names. -/
theorem exists_computableLipschitz_not_differentiableAt {x : Cantor}
    (hx : ¬IsComputablyRandom x) :
    ∃ f : ComputableLipschitz, ¬DifferentiableAt ℝ f.toFun (realOf x) := by
  rw [IsComputablyRandom, not_forall] at hx
  obtain ⟨d, hd⟩ := hx
  exact exists_computableLipschitz_not_differentiableAt_of_succeeds (not_not.mp hd)

end AlgorithmicRandomness
