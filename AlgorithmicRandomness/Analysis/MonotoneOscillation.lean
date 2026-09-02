/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.InfiniteUpperDerivative

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

end AlgorithmicRandomness
