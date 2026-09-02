/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.InfiniteUpperDerivative
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Chords of a non-differentiable monotone function

The oscillating construction needs two families of chords around `z`, at arbitrarily small width:
some with slope above a threshold, and some with slope *below* a smaller threshold and with `z` in
their middle third. The middle-third condition is what later lets the covering family select a cell
that still contains `z`.

The one-sided chords at `z` are what non-differentiability directly provides, and they place `z` at
an endpoint. Turning a small one-sided chord into a two-sided one with `z` in the middle third
costs an extension on the other side, whose mass has to be paid for. The bound used for that
extension cannot be an arbitrary one: it must be close to the *infimum of eventual upper bounds*,
since the middle-third average of a small slope and a large one only stays small when the large one
is itself close to that infimum. That is the whole content of the estimate below.
-/

open Filter Topology

open scoped NNRat NNReal

namespace AlgorithmicRandomness

namespace ComputableMonotone

variable (f : ComputableMonotone)

/-- The eventual upper bounds on the chord slopes at `z`. -/
private def slopeBounds (f : ComputableMonotone) (z : ℝ) : Set ℝ :=
  {c : ℝ | ∃ ε > 0, ∀ y, y ≠ z → |y - z| < ε → slope f.addIdentity.toFun z y ≤ c}

private theorem slope_addIdentity_eq (f : ComputableMonotone) {z y : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) (hne : y ≠ z) :
    slope f.addIdentity.toFun z y = slope f.toFun z y + 1 :=
  slope_addIdentity f hz hy (Ne.symm hne)

private theorem one_le_slope_addIdentity (f : ComputableMonotone) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a < b) :
    1 ≤ slope f.addIdentity.toFun a b := by
  rw [slope_addIdentity f ha hb (ne_of_lt hab), slope_def_field]
  have h := f.monotone_toFun hab.le
  have : 0 ≤ (f.toFun b - f.toFun a) / (b - a) := by
    apply div_nonneg <;> linarith
  linarith

private theorem slopeBounds_nonempty {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (hfinite : FiniteUpperDerivativeAt f.toFun z) : (slopeBounds f z).Nonempty := by
  obtain ⟨C, ε, hε, hC⟩ := finiteUpperDerivativeAt_iff.mp hfinite
  refine ⟨C + 1, min ε (min z (1 - z)), lt_min hε (lt_min hz.1 (by linarith [hz.2])),
    fun y hy hyz ↦ ?_⟩
  have h1 : |y - z| < ε := lt_of_lt_of_le hyz (min_le_left _ _)
  have h2 : |y - z| < z := lt_of_lt_of_le hyz (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : |y - z| < 1 - z := lt_of_lt_of_le hyz (le_trans (min_le_right _ _) (min_le_right _ _))
  rw [abs_lt] at h2 h3
  have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [h2.1], by linarith [h3.2]⟩
  rw [slope_addIdentity_eq f (Set.Ioo_subset_Icc_self hz) hy01 hy]
  have := hC y hy h1
  linarith

private theorem slopeBounds_bddBelow {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    BddBelow (slopeBounds f z) := by
  refine ⟨1, fun c hc ↦ ?_⟩
  obtain ⟨ε, hε, h⟩ := hc
  set d : ℝ := min ε (min z (1 - z)) / 2 with hd
  have hdpos : 0 < d := by
    have := lt_min hε (lt_min hz.1 (by linarith [hz.2] : (0:ℝ) < 1 - z))
    rw [hd]
    linarith
  have hdlt : d < ε := by
    have h1 : min ε (min z (1 - z)) ≤ ε := min_le_left _ _
    rw [hd]
    linarith [hε]
  have hd1 : d < 1 - z := by
    have h1 : min ε (min z (1 - z)) ≤ 1 - z :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : (0:ℝ) < 1 - z := by linarith [hz.2]
    rw [hd]
    linarith
  have hne : z + d ≠ z := by linarith
  have habs : |z + d - z| < ε := by
    rw [show z + d - z = d by ring, abs_of_pos hdpos]
    exact hdlt
  refine le_trans ?_ (h (z + d) hne habs)
  refine f.one_le_slope_addIdentity (Set.Ioo_subset_Icc_self hz) ⟨by linarith [hz.1], by linarith⟩
    (by linarith)

/-- The infimum of the eventual upper bounds: the sharp constant the extension estimate needs. -/
private noncomputable def slopeTop (f : ComputableMonotone) (z : ℝ) : ℝ :=
  sInf (slopeBounds f z)

private theorem eventually_le_slopeTop_add {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (hfinite : FiniteUpperDerivativeAt f.toFun z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ y, y ≠ z → |y - z| < ε → slope f.addIdentity.toFun z y ≤ slopeTop f z + δ := by
  obtain ⟨c, hcmem, hclt⟩ := exists_lt_of_csInf_lt (slopeBounds_nonempty f hz hfinite)
    (show slopeTop f z < slopeTop f z + δ by linarith)
  obtain ⟨ε, hε, h⟩ := hcmem
  exact ⟨ε, hε, fun y hy hyz ↦ le_trans (h y hy hyz) hclt.le⟩

private theorem exists_gt_slopeTop_sub {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y, y ≠ z ∧ |y - z| < ε ∧ slopeTop f z - δ < slope f.addIdentity.toFun z y := by
  by_contra hcon
  have hmem : slopeTop f z - δ ∈ slopeBounds f z := by
    refine ⟨ε, hε, fun y hy hyz ↦ ?_⟩
    by_contra hlt
    exact hcon ⟨y, hy, hyz, lt_of_not_ge hlt⟩
  have hle : slopeTop f z ≤ slopeTop f z - δ := csInf_le (slopeBounds_bddBelow f hz) hmem
  linarith

/-- Non-differentiability produces slopes below the infimum of eventual upper bounds, arbitrarily
close to `z`. -/
private theorem exists_lt_of_not_differentiableAt {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (hfinite : FiniteUpperDerivativeAt f.toFun z) (hnot : ¬DifferentiableAt ℝ f.toFun z) :
    ∃ m : ℝ, m < slopeTop f z ∧
      ∀ ε > 0, ∃ y, y ≠ z ∧ |y - z| < ε ∧ slope f.addIdentity.toFun z y < m := by
  by_contra hcon
  have hlow : ∀ m : ℝ, m < slopeTop f z →
      ∃ ε > 0, ∀ y, y ≠ z → |y - z| < ε → m ≤ slope f.addIdentity.toFun z y := by
    intro m hm
    by_contra hno
    refine hcon ⟨m, hm, fun ε hε ↦ ?_⟩
    by_contra hno2
    exact hno ⟨ε, hε, fun y hy hyz ↦ by
      by_contra hlt
      exact hno2 ⟨y, hy, hyz, lt_of_not_ge hlt⟩⟩
  have htend : Filter.Tendsto (slope f.addIdentity.toFun z) (nhdsWithin z {z}ᶜ)
      (nhds (slopeTop f z)) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro δ hδ
    obtain ⟨ε₁, hε₁, h₁⟩ := eventually_le_slopeTop_add f hz hfinite (half_pos hδ)
    obtain ⟨ε₂, hε₂, h₂⟩ := hlow (slopeTop f z - δ / 2) (by linarith)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun {y} hy hyz ↦ ?_⟩
    have hyne : y ≠ z := hy
    rw [Real.dist_eq] at hyz ⊢
    have hb1 := h₁ y hyne (lt_of_lt_of_le hyz (min_le_left _ _))
    have hb2 := h₂ y hyne (lt_of_lt_of_le hyz (min_le_right _ _))
    rw [abs_lt]
    constructor <;> linarith
  have hderiv : DifferentiableAt ℝ f.addIdentity.toFun z :=
    (hasDerivAt_iff_tendsto_slope.mpr htend).differentiableAt
  exact hnot ((f.differentiableAt_addIdentity_iff hz).mp hderiv)

private theorem slope_min_max {F : ℝ → ℝ} {z y : ℝ} (hne : y ≠ z) :
    slope F (min y z) (max y z) = slope F z y := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, slope_comm]
  · rw [min_eq_right h.le, max_eq_left h.le]

/-- **The chord gap.** Non-differentiability with a finite upper derivative produces chords of
arbitrarily small width with slope above a threshold, and chords of arbitrarily small width with
`z` in their middle third and slope below a smaller threshold. -/
private theorem exists_raw_chord_gap {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (hfinite : FiniteUpperDerivativeAt f.toFun z) (hnot : ¬DifferentiableAt ℝ f.toFun z) :
    ∃ low high : ℚ≥0, low < high ∧
      (∀ ε > 0, ∃ a b : ℝ,
        0 < a ∧ a < b ∧ b < 1 ∧ z ∈ Set.Icc a b ∧ b - a < ε ∧
        ((high : ℚ≥0) : ℝ) < slope f.addIdentity.toFun a b) ∧
      (∀ ε > 0, ∃ a b : ℝ,
        0 < a ∧ a < b ∧ b < 1 ∧ b - a < ε ∧
        a + (b - a) / 3 ≤ z ∧ z ≤ a + 2 * (b - a) / 3 ∧
        slope f.addIdentity.toFun a b < ((low : ℚ≥0) : ℝ)) := by
  obtain ⟨m, hmM, hmlow⟩ := exists_lt_of_not_differentiableAt f hz hfinite hnot
  set M : ℝ := slopeTop f z with hM
  set δ : ℝ := (M - m) / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨εa, hεa, hbound⟩ := eventually_le_slopeTop_add f hz hfinite hδ
  have hzpos := hz.1
  have hz1 : z < 1 := hz.2
  -- the slopes are at least one, so `m` exceeds one
  have hm1 : 1 < m := by
    obtain ⟨y, hy, hyz, hlt⟩ := hmlow (min z (1 - z)) (lt_min hzpos (by linarith))
    have h2 : |y - z| < z := lt_of_lt_of_le hyz (min_le_left _ _)
    have h3 : |y - z| < 1 - z := lt_of_lt_of_le hyz (min_le_right _ _)
    rw [abs_lt] at h2 h3
    have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [h2.1], by linarith [h3.2]⟩
    have hone : 1 ≤ slope f.addIdentity.toFun (min y z) (max y z) := by
      refine f.one_le_slope_addIdentity ?_ ?_ ?_
      · rcases lt_or_gt_of_ne hy with h | h
        · rw [min_eq_left h.le]; exact hy01
        · rw [min_eq_right h.le]; exact Set.Ioo_subset_Icc_self hz
      · rcases lt_or_gt_of_ne hy with h | h
        · rw [max_eq_right h.le]; exact Set.Ioo_subset_Icc_self hz
        · rw [max_eq_left h.le]; exact hy01
      · rcases lt_or_gt_of_ne hy with h | h
        · rw [min_eq_left h.le, max_eq_right h.le]; exact h
        · rw [min_eq_right h.le, max_eq_left h.le]; exact h
    rw [slope_min_max hy] at hone
    linarith
  have hgap : (2 * m + M + 3 * δ) / 3 < M - δ := by rw [hδdef]; linarith
  obtain ⟨lq, hlq1, hlq2⟩ := exists_rat_btwn hgap
  obtain ⟨hq, hhq1, hhq2⟩ := exists_rat_btwn hlq2
  have hlq0 : (0 : ℚ) ≤ lq := by
    have : (0 : ℝ) < (lq : ℝ) := by
      refine lt_trans ?_ hlq1
      rw [hδdef]
      linarith
    exact_mod_cast this.le
  have hlqhq : lq < hq := by exact_mod_cast (hhq1 : (lq : ℝ) < (hq : ℝ))
  have hhq0 : (0 : ℚ) ≤ hq := le_of_lt (lt_of_le_of_lt hlq0 hlqhq)
  have hcoeL : ((lq.toNNRat : ℚ≥0) : ℝ) = (lq : ℝ) := by
    exact_mod_cast congrArg (fun r : ℚ ↦ (r : ℝ)) (Rat.coe_toNNRat lq hlq0)
  have hcoeH : ((hq.toNNRat : ℚ≥0) : ℝ) = (hq : ℝ) := by
    exact_mod_cast congrArg (fun r : ℚ ↦ (r : ℝ)) (Rat.coe_toNNRat hq hhq0)
  refine ⟨lq.toNNRat, hq.toNNRat, ?_, ?_, ?_⟩
  · exact (Rat.toNNRat_lt_toNNRat_iff (lt_of_le_of_lt hlq0 hlqhq)).mpr hlqhq
  · -- the large chords
    intro ε hε
    obtain ⟨y, hy, hyz, hlt⟩ := exists_gt_slopeTop_sub f hz hδ
      (lt_min hε (lt_min hzpos (by linarith : (0:ℝ) < 1 - z)))
    have h1 : |y - z| < ε := lt_of_lt_of_le hyz (min_le_left _ _)
    have h2 : |y - z| < z := lt_of_lt_of_le hyz (le_trans (min_le_right _ _) (min_le_left _ _))
    have h3 : |y - z| < 1 - z :=
      lt_of_lt_of_le hyz (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [abs_lt] at h2 h3
    refine ⟨min y z, max y z, ?_, ?_, ?_, ⟨min_le_right _ _, le_max_right _ _⟩, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hy with h | h
      · rw [min_eq_left h.le]; linarith [h2.1]
      · rw [min_eq_right h.le]; exact hzpos
    · rcases lt_or_gt_of_ne hy with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h
    · rcases lt_or_gt_of_ne hy with h | h
      · rw [max_eq_right h.le]; exact hz1
      · rw [max_eq_left h.le]; linarith [h3.2]
    · rcases lt_or_gt_of_ne hy with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]
        rw [abs_lt] at h1
        linarith [h1.1]
      · rw [min_eq_right h.le, max_eq_left h.le]
        rw [abs_lt] at h1
        linarith [h1.2]
    · rw [slope_min_max hy, hcoeH]
      have : (hq : ℝ) < M - δ := hhq2
      linarith
  · -- the small middle-third chords
    intro ε hε
    obtain ⟨y, hy, hyz, hlt⟩ := hmlow (min εa (min (2 * ε / 3) (min z (1 - z))))
      (lt_min hεa (lt_min (by linarith) (lt_min hzpos (by linarith))))
    have ha : |y - z| < εa := lt_of_lt_of_le hyz (min_le_left _ _)
    have hb : |y - z| < 2 * ε / 3 :=
      lt_of_lt_of_le hyz (le_trans (min_le_right _ _) (min_le_left _ _))
    have hc : |y - z| < z :=
      lt_of_lt_of_le hyz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_left _ _)))
    have hd : |y - z| < 1 - z :=
      lt_of_lt_of_le hyz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_right _ _)))
    have hc' := abs_lt.mp hc
    have hd' := abs_lt.mp hd
    rw [hcoeL]
    rcases lt_or_gt_of_ne hy with hyl | hyg
    · -- `y < z`: extend to the right
      set t : ℝ := z - y with ht
      have htpos : 0 < t := by rw [ht]; linarith
      have htabs : |y - z| = t := by rw [ht, abs_of_neg (by linarith : y - z < 0)]; ring
      refine ⟨y, z + t / 2, by linarith [hc'.1], by linarith, by
        rw [htabs] at hd; linarith, ?_, by linarith, by linarith, ?_⟩
      · rw [htabs] at hb; linarith
      · have hne2 : z + t / 2 ≠ z := by linarith
        have habs2 : |z + t / 2 - z| < εa := by
          rw [show z + t / 2 - z = t / 2 by ring, abs_of_pos (by linarith)]
          rw [htabs] at ha
          linarith
        have hup := hbound (z + t / 2) hne2 habs2
        have hlow2 : slope f.addIdentity.toFun z y < m := hlt
        rw [slope_def_field] at hup hlow2 ⊢
        have h1 : f.addIdentity.toFun (z + t / 2) - f.addIdentity.toFun z ≤ (M + δ) * (t / 2) := by
          rw [div_le_iff₀ (by linarith : (0:ℝ) < z + t / 2 - z)] at hup
          linarith [hup]
        have h2 : f.addIdentity.toFun z - f.addIdentity.toFun y < m * t := by
          rw [div_lt_iff_of_neg (by linarith : y - z < 0)] at hlow2
          linarith [hlow2]
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < z + t / 2 - y)]
        have hlq : (2 * m + M + 3 * δ) / 3 < (lq : ℝ) := hlq1
        nlinarith [h1, h2, hlq, htpos]
    · -- `z < y`: extend to the left
      set t : ℝ := y - z with ht
      have htpos : 0 < t := by rw [ht]; linarith
      have htabs : |y - z| = t := by rw [ht, abs_of_pos (by linarith : 0 < y - z)]
      refine ⟨z - t / 2, y, by
        rw [htabs] at hc; linarith, by linarith, by rw [htabs] at hd; linarith, ?_, by linarith,
        by linarith, ?_⟩
      · rw [htabs] at hb; linarith
      · have hne2 : z - t / 2 ≠ z := by linarith
        have habs2 : |z - t / 2 - z| < εa := by
          rw [show z - t / 2 - z = -(t / 2) by ring, abs_neg, abs_of_pos (by linarith)]
          rw [htabs] at ha
          linarith
        have hup := hbound (z - t / 2) hne2 habs2
        have hlow2 : slope f.addIdentity.toFun z y < m := hlt
        rw [slope_def_field] at hup hlow2 ⊢
        have h1 : f.addIdentity.toFun z - f.addIdentity.toFun (z - t / 2) ≤ (M + δ) * (t / 2) := by
          rw [div_le_iff_of_neg (by linarith : z - t / 2 - z < 0)] at hup
          linarith [hup]
        have h2 : f.addIdentity.toFun y - f.addIdentity.toFun z < m * t := by
          rw [div_lt_iff₀ (by linarith : (0:ℝ) < y - z)] at hlow2
          linarith [hlow2]
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < y - (z - t / 2))]
        have hlq : (2 * m + M + 3 * δ) / 3 < (lq : ℝ) := hlq1
        nlinarith [h1, h2, hlq, htpos]

end ComputableMonotone

/-! ## Selecting a grid that recurs

The two cell families are produced one scale at a time, each time by the covering lemma, which may
return a different grid at each scale. Since the family is finite, one grid is returned infinitely
often; that grid is the one the construction fixes. -/

private theorem exists_grid_with_infinite_fiber (grids : Finset AffineDyadicGrid)
    (P : ℕ → AffineDyadicGrid → Prop) (h : ∀ n, ∃ G ∈ grids, P n G) :
    ∃ G ∈ grids, Set.Infinite {n | P n G} := by
  classical
  choose G hG hP using h
  let pick : ℕ → ↥grids := fun n ↦ ⟨G n, hG n⟩
  obtain ⟨G₀, hfiber⟩ := Finite.exists_infinite_fiber pick
  refine ⟨G₀, G₀.property, ?_⟩
  have hinf : (pick ⁻¹' ({G₀} : Set ↥grids)).Infinite := Set.infinite_coe_iff.mp hfiber
  refine hinf.mono ?_
  intro n hn
  have heq : G n = (G₀ : AffineDyadicGrid) := by
    have hpick : pick n = G₀ := by simpa using hn
    exact congrArg Subtype.val hpick
  simpa [heq] using hP n

/-! ## Threshold arithmetic

Three selections, each independent of the geometry: a covering ratio close enough to one, two
thresholds strictly inside the resulting gap, and a precision whose margin preserves all three
strict inequalities. -/

private theorem exists_coverRatio {low high : ℚ≥0} (h : low < high) :
    ∃ α : ℚ, 1 < α ∧ α < 4 / 3 ∧
      (α : ℝ) * ((low : ℚ≥0) : ℝ) < ((high : ℚ≥0) : ℝ) / (α : ℝ) := by
  have hlq : ((low : ℚ≥0) : ℚ) < ((high : ℚ≥0) : ℚ) := by exact_mod_cast h
  have hhpos : (0 : ℚ) < ((high : ℚ≥0) : ℚ) := lt_of_le_of_lt (by positivity) hlq
  rcases eq_or_lt_of_le (show (0 : ℚ) ≤ ((low : ℚ≥0) : ℚ) by positivity) with hlow | hlow
  · refine ⟨7 / 6, by norm_num, by norm_num, ?_⟩
    have hl0 : ((low : ℚ≥0) : ℝ) = 0 := by exact_mod_cast hlow.symm
    have hh0 : (0 : ℝ) < ((high : ℚ≥0) : ℝ) := by exact_mod_cast hhpos
    rw [hl0, mul_zero]
    positivity
  · set l : ℚ := ((low : ℚ≥0) : ℚ) with hl
    set hh : ℚ := ((high : ℚ≥0) : ℚ) with hhdef
    set s : ℚ := hh / l - 1 with hs
    have hspos : 0 < s := by
      rw [hs, sub_pos, lt_div_iff₀ hlow]
      linarith
    set t : ℚ := min (1 / 6) (s / 4) with ht
    have htpos : 0 < t := lt_min (by norm_num) (by linarith)
    have ht6 : t ≤ 1 / 6 := min_le_left _ _
    have hts : t ≤ s / 4 := min_le_right _ _
    have hsl : s * l = hh - l := by
      rw [hs]
      field_simp
    have htt : t * t ≤ (1 / 6) * (s / 4) := mul_le_mul ht6 hts htpos.le (by norm_num)
    have hkey2 : 2 * t + t * t < s := by linarith
    have hmul : (2 * t + t * t) * l < s * l := mul_lt_mul_of_pos_right hkey2 hlow
    have hkey : (1 + t) * (1 + t) * l < hh := by nlinarith [hmul, hsl]
    refine ⟨1 + t, by linarith, by linarith, ?_⟩
    have hαpos : (0 : ℝ) < ((1 + t : ℚ) : ℝ) := by
      have : (0 : ℚ) < 1 + t := by linarith
      exact_mod_cast this
    rw [lt_div_iff₀ hαpos]
    have hcast : (((1 + t) * (1 + t) * l : ℚ) : ℝ) < ((hh : ℚ) : ℝ) := by exact_mod_cast hkey
    rw [hl, hhdef] at hcast
    push_cast at hcast ⊢
    nlinarith [hcast]

private theorem exists_thresholds {A B : ℝ} (hA : 0 ≤ A) (hAB : A < B) :
    ∃ beta gamma : ℚ≥0, A < ((beta : ℚ≥0) : ℝ) ∧ ((beta : ℚ≥0) : ℝ) < ((gamma : ℚ≥0) : ℝ) ∧
      ((gamma : ℚ≥0) : ℝ) < B := by
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hAB
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hb2
  have hb0 : (0 : ℚ) ≤ b := by
    have : (0 : ℝ) ≤ (b : ℝ) := le_trans hA hb1.le
    exact_mod_cast this
  have hc0 : (0 : ℚ) ≤ c := by
    have : (0 : ℝ) ≤ (c : ℝ) := le_trans (le_trans hA hb1.le) hc1.le
    exact_mod_cast this
  have hbcast : ((b.toNNRat : ℚ≥0) : ℝ) = (b : ℝ) := by
    exact_mod_cast congrArg (fun r : ℚ ↦ (r : ℝ)) (Rat.coe_toNNRat b hb0)
  have hccast : ((c.toNNRat : ℚ≥0) : ℝ) = (c : ℝ) := by
    exact_mod_cast congrArg (fun r : ℚ ↦ (r : ℝ)) (Rat.coe_toNNRat c hc0)
  exact ⟨b.toNNRat, c.toNNRat, by rw [hbcast]; exact hb1, by rw [hbcast, hccast]; exact hc1,
    by rw [hccast]; exact hc2⟩

private theorem exists_robustPrecision {A beta gamma B : ℝ} (h1 : A < beta) (h2 : beta < gamma)
    (h3 : gamma < B) :
    ∃ K : ℕ, A < beta - (2⁻¹ : ℝ) ^ K ∧ gamma + (2⁻¹ : ℝ) ^ K < B ∧
      beta + (2⁻¹ : ℝ) ^ K < gamma - (2⁻¹ : ℝ) ^ K := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < min (beta - A) (min (B - gamma) ((gamma - beta) / 2)) from
      lt_min (by linarith) (lt_min (by linarith) (by linarith)))
    (show (2⁻¹ : ℝ) < 1 by norm_num)
  have hm1 : (2⁻¹ : ℝ) ^ K < beta - A := lt_of_lt_of_le hK (min_le_left _ _)
  have hm2 : (2⁻¹ : ℝ) ^ K < B - gamma :=
    lt_of_lt_of_le hK (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm3 : (2⁻¹ : ℝ) ^ K < (gamma - beta) / 2 :=
    lt_of_lt_of_le hK (le_trans (min_le_right _ _) (min_le_right _ _))
  exact ⟨K, by linarith, by linarith, by linarith⟩

/-! ## The oscillation parameters and witness

Only the parameters enter the program. The two recurrence properties are used solely to prove that
the constructed martingale succeeds at `z`, so the classical selection of the two grids introduces
no dependence on an oracle. -/

/-- The executable data of the oscillating construction. -/
private structure OscillationParams where
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

private noncomputable def beta (P : OscillationParams) : ℝ :=
  ((NNRatCode.value P.betaCode : ℚ≥0) : ℝ)

private noncomputable def gamma (P : OscillationParams) : ℝ :=
  ((NNRatCode.value P.gammaCode : ℚ≥0) : ℝ)

private noncomputable def margin (P : OscillationParams) : ℝ := (2⁻¹ : ℝ) ^ P.precision

private theorem margin_pos (P : OscillationParams) : 0 < P.margin := by
  rw [margin]
  positivity

private theorem beta_add_margin_lt (P : OscillationParams) :
    P.beta + P.margin < P.gamma - P.margin := P.robustGap

private theorem one_lt_ratio (P : OscillationParams) (hβ : 0 ≤ P.beta) :
    1 < (P.gamma - P.margin) / (P.beta + P.margin) := by
  have hpos : 0 < P.beta + P.margin := by linarith [P.margin_pos]
  rw [lt_div_iff₀ hpos]
  linarith [P.beta_add_margin_lt]

end OscillationParams

/-- The analytic content: the two selected grids each carry cells of arbitrarily small width whose
slopes clear the thresholds by the margin. -/
private structure OscillationWitness (F : ComputableMonotone) (z : ℝ) extends
    OscillationParams where
  /-- Betting cells of arbitrarily small width with slope above `γ + margin`. -/
  arbitrarily_small_high : ∀ ε : ℝ, 0 < ε → ∃ σ : BitString,
    z ∈ betGrid.interval σ ∧ betGrid.width σ < ε ∧
      ((NNRatCode.value gammaCode : ℚ≥0) : ℝ) + (2⁻¹ : ℝ) ^ precision
        < ((affineSlope F betGrid σ : ℝ≥0) : ℝ)
  /-- Waiting cells of arbitrarily small width with slope below `β - margin`. -/
  arbitrarily_small_low : ∀ ε : ℝ, 0 < ε → ∃ σ : BitString,
    z ∈ waitGrid.interval σ ∧ waitGrid.width σ < ε ∧
      ((affineSlope F waitGrid σ : ℝ≥0) : ℝ)
        < ((NNRatCode.value betaCode : ℚ≥0) : ℝ) - (2⁻¹ : ℝ) ^ precision

namespace ComputableMonotone

variable (f : ComputableMonotone)

/-! ## Cells at a prescribed scale

All slope algebra lives here, so the pigeonhole step below is purely combinatorial. -/

private theorem exists_high_cell_at_scale {z : ℝ} {high : ℚ≥0} {α : ℚ} (hα : 1 < α)
    {grids : Finset AffineDyadicGrid}
    (houter : ∀ {x y : ℝ}, 0 < x → x < y → y < 1 →
      ∃ G ∈ grids, ∃ σ, Set.Icc x y ⊆ G.interval σ ∧ G.width σ < (α : ℝ) * (y - x))
    (hchords : ∀ ε > 0, ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ z ∈ Set.Icc a b ∧ b - a < ε ∧
      ((high : ℚ≥0) : ℝ) < slope f.addIdentity.toFun a b)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c < ((high : ℚ≥0) : ℝ) / (α : ℝ)) (n : ℕ) :
    ∃ G ∈ grids, ∃ σ, z ∈ G.interval σ ∧ G.width σ < (2⁻¹ : ℝ) ^ n ∧
      c < ((affineSlope f.addIdentity G σ : ℝ≥0) : ℝ) := by
  have hαR : (0 : ℝ) < (α : ℝ) := by
    have : (0 : ℚ) < α := by linarith
    exact_mod_cast this
  obtain ⟨a, b, ha, hab, hb, hzab, hwidth, hslope⟩ :=
    hchords ((2⁻¹ : ℝ) ^ n / (α : ℝ)) (by positivity)
  obtain ⟨G, hG, σ, hsub, hcell⟩ := houter ha hab hb
  have hba : (0 : ℝ) < b - a := by linarith
  have hwpos : (0 : ℝ) < G.width σ := G.width_pos σ
  have hends : G.left σ ≤ a ∧ b ≤ G.right σ := by
    have h1 := hsub (Set.left_mem_Icc.mpr hab.le)
    have h2 := hsub (Set.right_mem_Icc.mpr hab.le)
    rw [AffineDyadicGrid.interval, Set.mem_Icc] at h1 h2
    exact ⟨h1.1, h2.2⟩
  refine ⟨G, hG, σ, hsub hzab, ?_, ?_⟩
  · refine lt_trans hcell ?_
    rw [lt_div_iff₀ hαR] at hwidth
    nlinarith [hwidth]
  · have hnum : ((high : ℚ≥0) : ℝ) * (b - a) < f.addIdentity.toFun b - f.addIdentity.toFun a := by
      rw [slope_def_field, lt_div_iff₀ hba] at hslope
      linarith
    have hmono : f.addIdentity.toFun b - f.addIdentity.toFun a
        ≤ f.addIdentity.toFun (G.right σ) - f.addIdentity.toFun (G.left σ) := by
      have h1 := f.addIdentity.monotone_toFun hends.1
      have h2 := f.addIdentity.monotone_toFun hends.2
      linarith
    have hw : G.right σ - G.left σ = G.width σ := by
      rw [AffineDyadicGrid.right]
      ring
    rw [coe_affineSlope, slope_def_field, hw, lt_div_iff₀ hwpos]
    have hstep : c * G.width σ ≤ c * ((α : ℝ) * (b - a)) :=
      mul_le_mul_of_nonneg_left hcell.le hc0
    have hstep2 : c * ((α : ℝ) * (b - a)) ≤ ((high : ℚ≥0) : ℝ) * (b - a) := by
      have hle : c * (α : ℝ) ≤ ((high : ℚ≥0) : ℝ) := by
        rw [lt_div_iff₀ hαR] at hc
        linarith
      nlinarith [hba]
    linarith

private theorem exists_low_cell_at_scale {z : ℝ} {low : ℚ≥0} {α : ℚ} (hα1 : 1 < α)
    (hα2 : α < 4 / 3) {grids : Finset AffineDyadicGrid}
    (hinner : ∀ {x y : ℝ}, 0 < x → x < y → y < 1 →
      ∃ G ∈ grids, ∃ σ, G.interval σ ⊆ Set.Icc x y ∧ y - x < (α : ℝ) * G.width σ)
    (hchords : ∀ ε > 0, ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ b - a < ε ∧
      a + (b - a) / 3 ≤ z ∧ z ≤ a + 2 * (b - a) / 3 ∧
      slope f.addIdentity.toFun a b < ((low : ℚ≥0) : ℝ))
    {c : ℝ} (hc : (α : ℝ) * ((low : ℚ≥0) : ℝ) < c) (n : ℕ) :
    ∃ G ∈ grids, ∃ σ, z ∈ G.interval σ ∧ G.width σ < (2⁻¹ : ℝ) ^ n ∧
      ((affineSlope f.addIdentity G σ : ℝ≥0) : ℝ) < c := by
  have hαR : (1 : ℝ) < (α : ℝ) := by exact_mod_cast hα1
  have hα2R : (α : ℝ) < 4 / 3 := by
    have hcast : ((α : ℚ) : ℝ) < ((4 / 3 : ℚ) : ℝ) := by exact_mod_cast hα2
    push_cast at hcast
    exact hcast
  obtain ⟨a, b, ha, hab, hb, hwidth, hlo, hhi, hslope⟩ := hchords ((2⁻¹ : ℝ) ^ n) (by positivity)
  obtain ⟨G, hG, σ, hsub, hcell⟩ := hinner ha hab hb
  have hba : (0 : ℝ) < b - a := by linarith
  have hwpos : (0 : ℝ) < G.width σ := G.width_pos σ
  have hends : a ≤ G.left σ ∧ G.right σ ≤ b := by
    have h := hsub
    rw [AffineDyadicGrid.interval] at h
    have h1 := h (Set.left_mem_Icc.mpr (G.left_lt_right σ).le)
    have h2 := h (Set.right_mem_Icc.mpr (G.left_lt_right σ).le)
    rw [Set.mem_Icc] at h1 h2
    exact ⟨h1.1, h2.2⟩
  have hw : G.right σ - G.left σ = G.width σ := by
    rw [AffineDyadicGrid.right]
    ring
  have hprod : (α : ℝ) * G.width σ < (4 / 3) * G.width σ := mul_lt_mul_of_pos_right hα2R hwpos
  have hbig : 3 * (b - a) / 4 < G.width σ := by linarith
  refine ⟨G, hG, σ, ?_, ?_, ?_⟩
  · rw [AffineDyadicGrid.interval, Set.mem_Icc]
    constructor
    · nlinarith [hends.2, hw, hbig, hlo]
    · nlinarith [hends.1, hw, hbig, hhi]
  · refine lt_of_le_of_lt ?_ hwidth
    linarith [hends.1, hends.2, hw]
  · have hmono : f.addIdentity.toFun (G.right σ) - f.addIdentity.toFun (G.left σ)
        ≤ f.addIdentity.toFun b - f.addIdentity.toFun a := by
      have h1 := f.addIdentity.monotone_toFun hends.1
      have h2 := f.addIdentity.monotone_toFun hends.2
      linarith
    have hnum : f.addIdentity.toFun b - f.addIdentity.toFun a
        < ((low : ℚ≥0) : ℝ) * (b - a) := by
      rw [slope_def_field, div_lt_iff₀ hba] at hslope
      linarith
    rw [coe_affineSlope, slope_def_field, hw, div_lt_iff₀ hwpos]
    have hlow0 : (0 : ℝ) ≤ ((low : ℚ≥0) : ℝ) := by positivity
    have hstep : ((low : ℚ≥0) : ℝ) * (b - a) ≤ ((low : ℚ≥0) : ℝ) * ((α : ℝ) * G.width σ) :=
      mul_le_mul_of_nonneg_left hcell.le hlow0
    nlinarith [hmono, hnum, hstep, hwpos, hc]

/-! ## The witness

Everything analytic is sealed here: non-differentiability, the infimum of eventual upper bounds,
the covering ratio, and the finite pigeonhole. The tree layer sees only the two recurrence
properties and the robust gap. -/

private theorem nonempty_oscillationWitness {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (hfinite : FiniteUpperDerivativeAt f.toFun z) (hnot : ¬DifferentiableAt ℝ f.toFun z) :
    Nonempty (OscillationWitness f.addIdentity z) := by
  classical
  obtain ⟨low, high, hlh, hhighChords, hlowChords⟩ := exists_raw_chord_gap f hz hfinite hnot
  obtain ⟨α, hα1, hα2, hαgap⟩ := exists_coverRatio hlh
  have hαpos : (0 : ℝ) < (α : ℝ) := by
    have : (0 : ℚ) < α := by linarith
    exact_mod_cast this
  have hA0 : (0 : ℝ) ≤ (α : ℝ) * ((low : ℚ≥0) : ℝ) := by positivity
  obtain ⟨beta, gamma, hAb, hbg, hgB⟩ := exists_thresholds hA0 hαgap
  obtain ⟨K, hK1, hK2, hK3⟩ := exists_robustPrecision hAb hbg hgB
  obtain ⟨grids, houter, hinner⟩ := exists_finite_affineDyadicGrids (α := α) hα1
  obtain ⟨Ghigh, hGh, hinfH⟩ := exists_grid_with_infinite_fiber grids
    (fun n G ↦ ∃ σ : BitString, z ∈ G.interval σ ∧ G.width σ < (2⁻¹ : ℝ) ^ n ∧
      ((gamma : ℚ≥0) : ℝ) + (2⁻¹ : ℝ) ^ K < ((affineSlope f.addIdentity G σ : ℝ≥0) : ℝ))
    (fun n ↦ exists_high_cell_at_scale f hα1 houter hhighChords
      (by positivity) hK2 n)
  obtain ⟨Glow, hGl, hinfL⟩ := exists_grid_with_infinite_fiber grids
    (fun n G ↦ ∃ σ : BitString, z ∈ G.interval σ ∧ G.width σ < (2⁻¹ : ℝ) ^ n ∧
      ((affineSlope f.addIdentity G σ : ℝ≥0) : ℝ) < ((beta : ℚ≥0) : ℝ) - (2⁻¹ : ℝ) ^ K)
    (fun n ↦ exists_low_cell_at_scale f hα1 hα2 hinner hlowChords hK1 n)
  obtain ⟨bc, hbc⟩ := NNRatCode.value_surjective beta
  obtain ⟨gc, hgc⟩ := NNRatCode.value_surjective gamma
  refine ⟨{
      betGrid := Ghigh
      waitGrid := Glow
      betaCode := bc
      gammaCode := gc
      precision := K
      robustGap := ?_
      arbitrarily_small_high := ?_
      arbitrarily_small_low := ?_ }⟩
  · rw [hbc, hgc]
    exact hK3
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (show (2⁻¹ : ℝ) < 1 by norm_num)
    obtain ⟨n, hnmem, hnN⟩ := hinfH.exists_gt N
    obtain ⟨σ, hσz, hσw, hσs⟩ := hnmem
    refine ⟨σ, hσz, lt_trans hσw (lt_of_le_of_lt ?_ hN), ?_⟩
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_of_lt hnN)
    · rw [hgc]
      exact hσs
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (show (2⁻¹ : ℝ) < 1 by norm_num)
    obtain ⟨n, hnmem, hnN⟩ := hinfL.exists_gt N
    obtain ⟨σ, hσz, hσw, hσs⟩ := hnmem
    refine ⟨σ, hσz, lt_trans hσw (lt_of_le_of_lt ?_ hN), ?_⟩
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_of_lt hnN)
    · rw [hbc]
      exact hσs

end ComputableMonotone

end AlgorithmicRandomness
