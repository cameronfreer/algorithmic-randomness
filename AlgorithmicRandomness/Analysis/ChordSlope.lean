/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Separation.Basic

/-!
# Chords across shrinking intervals

If `f` is differentiable at `x`, then the slope of the chord across any interval containing `x`
tends to `f' x` as the interval shrinks. Contrapositively, exhibiting chord slopes that fail to
converge refutes differentiability.

The hypotheses are deliberately minimal: the intervals must *contain* `x`, have positive width,
and shrink. They need not be nested, and neither endpoint need be distinct from `x`. That last
point is why this is proved from `HasDerivAt.isLittleO` rather than from mathlib's
`hasDerivAtFilter_iff_tendsto_slope`: the latter works over the *punctured* neighbourhood, so an
endpoint landing exactly on `x` would need separate handling. Here it needs none — the estimate
is symmetric in the two endpoints and degenerates harmlessly.

The mechanism is one identity. Writing `R y = f y - f x - (y - x) * f'` for the remainder,

  `slope f a b - f' = (R b - R a) / (b - a)`,

and when `a ≤ x ≤ b` the two remainder bounds add to exactly the width, `|b - x| + |x - a| = b - a`,
so dividing by the positive width returns the constant from `isLittleO` unchanged.

This file is deliberately independent of the rest of the development: it imports only mathlib.
Everything here is a general fact about real functions and would be at home upstream.
-/

open Filter Topology

namespace AlgorithmicRandomness

/-! ## Two frequently attained values obstruct convergence -/

/-- A sequence that frequently takes two distinct values has no limit. Stated at `T1Space`
generality, which is all the argument uses: a limit differs from at least one of the two values,
and is then eventually different from it. -/
theorem not_exists_tendsto_of_frequently_eq {α Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {l : Filter α} {u : α → Y} {p q : Y} (hpq : p ≠ q)
    (hp : ∃ᶠ n in l, u n = p) (hq : ∃ᶠ n in l, u n = q) :
    ¬ ∃ L, Tendsto u l (𝓝 L) := by
  rintro ⟨L, hL⟩
  rcases eq_or_ne L p with rfl | hLp
  · exact (hq.and_eventually (hL.eventually_ne hpq)).exists.elim fun _ h ↦ h.2 h.1
  · exact (hp.and_eventually (hL.eventually_ne hLp)).exists.elim fun _ h ↦ h.2 h.1

/-! ## Chords across shrinking intervals -/

/-- **Chord slopes converge to the derivative.** Containment, positive width and shrinking are all
that is required; nesting is not. -/
theorem HasDerivAt.tendsto_chordSlope {f : ℝ → ℝ} {f' x : ℝ} {a b : ℕ → ℝ}
    (hf : HasDerivAt f f' x) (hmem : ∀ n, a n ≤ x ∧ x ≤ b n) (hlt : ∀ n, a n < b n)
    (hshrink : Tendsto (fun n ↦ b n - a n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ slope f (a n) (b n)) atTop (𝓝 f') := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- `ε / 2` from `isLittleO`, so that the triangle estimate lands strictly inside `ε`
  obtain ⟨δ, hδ, hδspec⟩ :=
    Metric.eventually_nhds_iff.mp (Asymptotics.isLittleO_iff.mp hf.isLittleO (half_pos hε))
  have hev : ∀ᶠ n in atTop, b n - a n < δ := by
    have h := hshrink
    rw [Metric.tendsto_nhds] at h
    filter_upwards [h δ hδ] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (sub_pos.mpr (hlt n))] at hn
    exact hn
  filter_upwards [hev] with n hn
  obtain ⟨hax, hxb⟩ := hmem n
  have hw : 0 < b n - a n := sub_pos.mpr (hlt n)
  have hRa := hδspec (y := a n) (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
  have hRb := hδspec (y := b n) (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul,
    abs_of_nonpos (a := a n - x) (by linarith)] at hRa
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul,
    abs_of_nonneg (a := b n - x) (by linarith)] at hRb
  obtain ⟨hRa1, hRa2⟩ := abs_le.mp hRa
  obtain ⟨hRb1, hRb2⟩ := abs_le.mp hRb
  have hkey : (f (b n) - f (a n)) / (b n - a n) - f'
      = ((f (b n) - f x - (b n - x) * f') - (f (a n) - f x - (a n - x) * f')) / (b n - a n) := by
    field_simp
    ring
  have hgap : ε / 2 * (b n - a n) < ε * (b n - a n) := by nlinarith
  rw [Real.dist_eq, slope_def_field, hkey, abs_div, abs_of_pos hw, div_lt_iff₀ hw, abs_lt]
  constructor <;> linarith

/-- **The contrapositive.** Chord slopes with no limit refute differentiability. -/
theorem not_differentiableAt_of_not_tendsto_chordSlope {f : ℝ → ℝ} {x : ℝ} {a b : ℕ → ℝ}
    (hmem : ∀ n, a n ≤ x ∧ x ≤ b n) (hlt : ∀ n, a n < b n)
    (hshrink : Tendsto (fun n ↦ b n - a n) atTop (𝓝 0))
    (hnot : ¬ ∃ L, Tendsto (fun n ↦ slope f (a n) (b n)) atTop (𝓝 L)) :
    ¬DifferentiableAt ℝ f x := by
  intro hdiff
  exact hnot ⟨deriv f x, HasDerivAt.tendsto_chordSlope hdiff.hasDerivAt hmem hlt hshrink⟩

end AlgorithmicRandomness
