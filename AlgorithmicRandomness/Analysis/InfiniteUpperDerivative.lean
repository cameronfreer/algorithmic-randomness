/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.AffineCovering
import AlgorithmicRandomness.Analysis.AffineSlope
import Mathlib.Analysis.Calculus.Deriv.Slope

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

/-! ## Finiteness along a computably random point

The covering grid maps the dyadic coordinate to the point's coordinate, so the sequence whose
randomness is used is an expansion of `u = (z - shift) / scale`, while the grid handed to the slope
bound is the covering grid itself. The inverse grid appears only inside affine preservation, which
is applied here as a black box.

Grids of the family that cannot cover an interval containing `z` are given the bound `0`, and the
family's bounds are aggregated by a sum of nonnegative terms rather than a supremum: `ℝ` has no
bottom element, and the sum dominates every term outright. -/

private theorem mem_dyadicInterval_of_mem_interval {G : AffineDyadicGrid} {z : ℝ} {σ : BitString}
    (h : z ∈ G.interval σ) : (z - G.shift) / G.scale ∈ dyadicInterval σ := by
  have hs := G.zero_lt_scale
  rw [AffineDyadicGrid.interval, Set.mem_Icc, AffineDyadicGrid.right, AffineDyadicGrid.left,
    AffineDyadicGrid.width] at h
  rw [dyadicInterval, Set.mem_Icc, dyadicRight]
  constructor
  · rw [le_div_iff₀ hs]
    linarith [h.1]
  · rw [div_le_iff₀ hs]
    nlinarith [h.2]

/-- Every grid of the family bounds the slopes over the cells that contain `z`. -/
private theorem exists_slope_bound_of_grid {z : ℝ} (hz : IsComputablyRandomReal z)
    (g : ComputableMonotone) (G : AffineDyadicGrid) :
    ∃ C : ℝ, ∀ σ : BitString, z ∈ G.interval σ →
      slope g.toFun (G.left σ) (G.right σ) ≤ C := by
  classical
  by_cases hGz : ∃ σ : BitString, z ∈ G.interval σ
  · obtain ⟨σ₀, hσ₀⟩ := hGz
    have hs := G.zero_lt_scale
    have hp : (0 : ℚ) < ((NNRatCode.value G.scaleCode : ℚ≥0) : ℚ) := by
      exact_mod_cast G.scale_pos
    have hu01 : (z - G.shift) / G.scale ∈ Set.Icc (0 : ℝ) 1 :=
      dyadicInterval_subset_unit σ₀ (mem_dyadicInterval_of_mem_interval hσ₀)
    have hzu : z = ((((NNRatCode.value G.scaleCode : ℚ≥0) : ℚ)) : ℝ)
        * ((z - G.shift) / G.scale + ((0 : ℤ) : ℝ))
        + (((RatCode.value G.shiftCode : ℚ)) : ℝ) := by
      have hscale : ((((NNRatCode.value G.scaleCode : ℚ≥0) : ℚ)) : ℝ) = G.scale := rfl
      have hshift : (((RatCode.value G.shiftCode : ℚ)) : ℝ) = G.shift := rfl
      rw [hscale, hshift]
      push_cast
      field_simp
      ring
    have hurand : IsComputablyRandomReal ((z - G.shift) / G.scale) :=
      isComputablyRandomReal_of_affine hp hu01 hzu hz
    have hune : ∀ q : ℚ, (z - G.shift) / G.scale ≠ (q : ℝ) := hurand.ne_rat
    obtain ⟨x, hxu, hxrand⟩ := hurand
    obtain ⟨C, hC⟩ := hxrand.affineSlope_bounded g G
    refine ⟨C, fun σ hσ ↦ ?_⟩
    have hmem : realOf x ∈ dyadicInterval σ := by
      rw [hxu]
      exact mem_dyadicInterval_of_mem_interval hσ
    have hne : ∀ q : ℚ, realOf x ≠ (q : ℝ) := by
      rw [hxu]
      exact hune
    rw [← initSeg_eq_of_mem_dyadicInterval_of_ne_rat hmem hne]
    exact hC σ.length
  · exact ⟨0, fun σ hσ ↦ absurd ⟨σ, hσ⟩ hGz⟩

/-- **Gate 4.** At a computably random real, every computable nondecreasing function has bounded
chord slopes nearby. -/
theorem IsComputablyRandomReal.finiteUpperDerivativeAt {z : ℝ} (hz : IsComputablyRandomReal z)
    (g : ComputableMonotone) : FiniteUpperDerivativeAt g.toFun z := by
  classical
  rw [finiteUpperDerivativeAt_iff]
  have hz01 := hz.mem_unit
  have hz0 : 0 < z := lt_of_le_of_ne hz01.1 fun h ↦ hz.ne_rat 0 (by rw [← h]; norm_num)
  have hz1 : z < 1 := lt_of_le_of_ne hz01.2 fun h ↦ hz.ne_rat 1 (by rw [h]; norm_num)
  obtain ⟨grids, houter, -⟩ := exists_finite_affineDyadicGrids (α := 2) (by norm_num)
  set D : AffineDyadicGrid → ℝ :=
    fun G ↦ max 0 (Classical.choose (exists_slope_bound_of_grid hz g G)) with hD
  set C : ℝ := ∑ G ∈ grids, D G with hC
  have hDle : ∀ G ∈ grids, D G ≤ C :=
    fun G hG ↦ Finset.single_le_sum (f := D) (fun H _ ↦ le_max_left _ _) hG
  have key : ∀ a b : ℝ, 0 < a → a < b → b < 1 → z ∈ Set.Icc a b →
      slope g.toFun a b ≤ 2 * C := by
    intro a b ha hab hb hzab
    obtain ⟨G, hG, σ, hsub, hwidth⟩ := houter ha hab hb
    have hzG : z ∈ G.interval σ := hsub hzab
    have hbound := Classical.choose_spec (exists_slope_bound_of_grid hz g G) σ hzG
    have hDG : slope g.toFun (G.left σ) (G.right σ) ≤ D G := le_trans hbound (le_max_right _ _)
    have hDnn : 0 ≤ D G := le_max_left _ _
    have hwpos : 0 < G.width σ := G.width_pos σ
    have hends : G.left σ ≤ a ∧ b ≤ G.right σ := by
      have h1 := hsub (Set.left_mem_Icc.mpr hab.le)
      have h2 := hsub (Set.right_mem_Icc.mpr hab.le)
      rw [AffineDyadicGrid.interval, Set.mem_Icc] at h1 h2
      exact ⟨h1.1, h2.2⟩
    have hmono : g.toFun b - g.toFun a ≤ g.toFun (G.right σ) - g.toFun (G.left σ) := by
      have h1 := g.monotone_toFun hends.1
      have h2 := g.monotone_toFun hends.2
      linarith
    have hw : G.right σ - G.left σ = G.width σ := by
      rw [AffineDyadicGrid.right]
      ring
    have hgap : g.toFun (G.right σ) - g.toFun (G.left σ) ≤ D G * G.width σ := by
      have h := hDG
      rw [slope_def_field, hw, div_le_iff₀ hwpos] at h
      exact h
    have hwidth' : G.width σ ≤ 2 * (b - a) := by
      push_cast at hwidth
      linarith
    have hstep : D G * G.width σ ≤ D G * (2 * (b - a)) :=
      mul_le_mul_of_nonneg_left hwidth' hDnn
    rw [slope_def_field, div_le_iff₀ (by linarith : (0:ℝ) < b - a)]
    calc g.toFun b - g.toFun a ≤ g.toFun (G.right σ) - g.toFun (G.left σ) := hmono
      _ ≤ D G * G.width σ := hgap
      _ ≤ D G * (2 * (b - a)) := hstep
      _ ≤ C * (2 * (b - a)) := mul_le_mul_of_nonneg_right (hDle G hG) (by linarith)
      _ = 2 * C * (b - a) := by ring
  refine ⟨2 * C, min z (1 - z), lt_min hz0 (by linarith), fun y hy hyz ↦ ?_⟩
  rw [abs_lt] at hyz
  have hmin := min_le_left z (1 - z)
  have hmin' := min_le_right z (1 - z)
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · rw [slope_comm]
    refine key y z (by linarith) hlt (by linarith) ?_
    exact Set.right_mem_Icc.mpr hlt.le
  · refine key z y (by linarith) hgt (by linarith) ?_
    exact Set.left_mem_Icc.mpr hgt.le

end AlgorithmicRandomness
