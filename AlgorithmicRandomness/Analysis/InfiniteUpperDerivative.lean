/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# A finite upper derivative, as a proposition

The upper derivative enters this development only through two uses: a bound witness near a point,
and its negation — slopes exceeding every proposed bound arbitrarily close by. Both are statements
about a witness and a neighbourhood, not about the numerical value of a limsup, so the notion is
defined as a proposition.

An `ℝ≥0∞`-valued definition would add `ENNReal.ofReal`, `Filter.limsup`, finiteness, and the
equivalence lemmas before yielding exactly the same `C` and `ε`. The pinned mathlib has slope and
derivative estimates but no ready-made upper-Dini-derivative API that would absorb that work. A
numerical interface can be derived later if some theorem genuinely needs the value.

The bound is non-strict, which is what makes the negation convenient: it produces slopes *strictly*
above every proposed bound, frequently near the point.
-/

open Filter Topology

namespace AlgorithmicRandomness

/-- The chord slopes at `z` are bounded above near `z`. -/
def FiniteUpperDerivativeAt (f : ℝ → ℝ) (z : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] z, slope f z y ≤ C

/-- The explicit-radius form, which is what a construction near `z` consumes. -/
theorem finiteUpperDerivativeAt_iff {f : ℝ → ℝ} {z : ℝ} :
    FiniteUpperDerivativeAt f z ↔
      ∃ C ε : ℝ, 0 < ε ∧ ∀ y, y ≠ z → |y - z| < ε → slope f z y ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hC
    obtain ⟨ε, hε, h⟩ := hC
    refine ⟨C, ε, hε, fun y hy hyz ↦ h ?_ hy⟩
    rwa [Real.dist_eq]
  · rintro ⟨C, ε, hε, h⟩
    refine ⟨C, ?_⟩
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨ε, hε, fun y hy hym ↦ h y hym ?_⟩
    rwa [Real.dist_eq] at hy

end AlgorithmicRandomness
