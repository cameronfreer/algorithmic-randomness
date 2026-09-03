/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.DyadicGrid

/-!
# The real number named by a point of Cantor space

`realOf x` is the real with binary expansion `x`, defined as the supremum of the left endpoints
of the prefix intervals rather than as a series.

The series definition `∑' i, (bit i) * 2^-(i+1)` would need a bridge from the `dyadicLeft` fold to
a finite sum, a summability proof, and a geometric tail estimate. The supremum needs only that the
prefix intervals are nested, which is a fact worth having on its own, and both containment bounds
then come from the same lemma: `le_ciSup` below, `ciSup_le` above. No `Summable` side condition
appears anywhere.

Because the intervals are *closed*, no "not a dyadic rational" hypothesis is needed: a point whose
expansion is eventually constant sits at an endpoint of every sufficiently long prefix interval
and is still contained in all of them, and `0` and `1` are covered like any other point.

The acceptance surface is the two-sided approximation by the interval width, and the resulting
convergence of both endpoint sequences to `realOf x`. Those are what pin the definition down: any
function contained in every prefix interval satisfies them, and they identify it uniquely.
-/

open Filter Topology

namespace AlgorithmicRandomness

/-- The real number with binary expansion `x`. -/
noncomputable def realOf (x : Cantor) : ℝ := ⨆ n, dyadicLeft (initSeg x n)

theorem bddAbove_prefix_left (x : Cantor) :
    BddAbove (Set.range fun n ↦ dyadicLeft (initSeg x n)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact dyadicLeft_le_one _

/-! ## Containment in every prefix interval -/

theorem dyadicLeft_initSeg_le_realOf (x : Cantor) (n : ℕ) :
    dyadicLeft (initSeg x n) ≤ realOf x :=
  le_ciSup (bddAbove_prefix_left x) n

theorem realOf_le_dyadicRight_initSeg (x : Cantor) (n : ℕ) :
    realOf x ≤ dyadicRight (initSeg x n) := by
  refine ciSup_le fun m ↦ ?_
  rcases le_total m n with h | h
  · calc dyadicLeft (initSeg x m) ≤ dyadicLeft (initSeg x n) :=
        dyadicLeft_mono_of_prefix (initSeg_prefix_of_le h)
      _ ≤ dyadicRight (initSeg x n) := (dyadicLeft_lt_dyadicRight _).le
  · calc dyadicLeft (initSeg x m) ≤ dyadicRight (initSeg x m) := (dyadicLeft_lt_dyadicRight _).le
      _ ≤ dyadicRight (initSeg x n) := dyadicRight_anti_of_prefix (initSeg_prefix_of_le h)

/-- **The containment property.** This is the whole point of the definition: the chord arguments
need a point inside every prefix interval, and closed intervals make that unconditional. -/
theorem realOf_mem_dyadicInterval (x : Cantor) (n : ℕ) :
    realOf x ∈ dyadicInterval (initSeg x n) :=
  ⟨dyadicLeft_initSeg_le_realOf x n, realOf_le_dyadicRight_initSeg x n⟩

theorem realOf_mem_unit (x : Cantor) : realOf x ∈ Set.Icc (0 : ℝ) 1 :=
  dyadicInterval_subset_unit _ (realOf_mem_dyadicInterval x 0)

/-! ## Approximation by the interval width -/

@[simp] theorem dyadicWidth_initSeg (x : Cantor) (n : ℕ) :
    dyadicWidth (initSeg x n) = (2 : ℝ)⁻¹ ^ n := by
  rw [dyadicWidth, length_initSeg]

theorem tendsto_prefix_width_zero (x : Cantor) :
    Tendsto (fun n ↦ dyadicWidth (initSeg x n)) atTop (𝓝 0) := by
  simp only [dyadicWidth_initSeg]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem realOf_sub_dyadicLeft_le_width (x : Cantor) (n : ℕ) :
    realOf x - dyadicLeft (initSeg x n) ≤ dyadicWidth (initSeg x n) := by
  have h := realOf_le_dyadicRight_initSeg x n
  rw [dyadicRight] at h
  linarith

theorem dyadicRight_sub_realOf_le_width (x : Cantor) (n : ℕ) :
    dyadicRight (initSeg x n) - realOf x ≤ dyadicWidth (initSeg x n) := by
  have h := dyadicLeft_initSeg_le_realOf x n
  rw [dyadicRight]
  linarith

/-! ## Both endpoints converge

These are not needed by the generic chord lemma, which asks only that the widths shrink. They are
the acceptance test for the supremum definition: they say the prefix endpoints really do close in
on `realOf x` from both sides, which is the content a series definition would have made explicit
and this one has to earn. -/

theorem tendsto_prefix_left_realOf (x : Cantor) :
    Tendsto (fun n ↦ dyadicLeft (initSeg x n)) atTop (𝓝 (realOf x)) := by
  have hlow : Tendsto (fun n ↦ realOf x - dyadicWidth (initSeg x n)) atTop (𝓝 (realOf x)) := by
    simpa using (tendsto_const_nhds (x := realOf x) (α := ℕ) (f := atTop)).sub
      (tendsto_prefix_width_zero x)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n ↦ by linarith [realOf_sub_dyadicLeft_le_width x n])
    (fun n ↦ dyadicLeft_initSeg_le_realOf x n)

theorem tendsto_prefix_right_realOf (x : Cantor) :
    Tendsto (fun n ↦ dyadicRight (initSeg x n)) atTop (𝓝 (realOf x)) := by
  have hhigh : Tendsto (fun n ↦ realOf x + dyadicWidth (initSeg x n)) atTop (𝓝 (realOf x)) := by
    simpa using (tendsto_const_nhds (x := realOf x) (α := ℕ) (f := atTop)).add
      (tendsto_prefix_width_zero x)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhigh
    (fun n ↦ realOf_le_dyadicRight_initSeg x n)
    (fun n ↦ by linarith [dyadicRight_sub_realOf_le_width x n])

/-! ## Uniqueness

Containment in every prefix interval determines the point, since two points in an interval differ
by at most its width. This is the converse half of the definition, and it is what makes the greedy
construction below identify `realOf` rather than merely produce something inside the intervals. -/

theorem eq_realOf_of_mem_all_dyadicInterval {z : ℝ} {x : Cantor}
    (h : ∀ n, z ∈ dyadicInterval (initSeg x n)) : z = realOf x := by
  simp only [dyadicInterval, Set.mem_Icc] at h
  have habs : ∀ n, |z - realOf x| ≤ dyadicWidth (initSeg x n) := by
    intro n
    obtain ⟨h1, h2⟩ := h n
    obtain ⟨h3, h4⟩ := realOf_mem_dyadicInterval x n
    rw [dyadicRight] at h2 h4
    rw [abs_le]
    constructor <;> linarith
  have hle : |z - realOf x| ≤ 0 := ge_of_tendsto' (tendsto_prefix_width_zero x) habs
  have := abs_nonpos_iff.mp hle
  linarith [sub_eq_zero.mp this]

/-! ## Every point of the unit interval has an expansion

The bits are chosen greedily: having narrowed to `[σ]`, take `true` exactly when `z` lies strictly
past the midpoint. The invariant is that `z` stays inside `[σ]`, and the midpoint is shared between
the two children (`dyadicRight_append_false_eq_left_append_true`), so one of them always keeps it.
-/

/-- The greedily chosen prefix of length `n`. -/
noncomputable def greedyPrefix (z : ℝ) : ℕ → BitString
  | 0 => []
  | n + 1 =>
      greedyPrefix z n ++
        [if dyadicRight (greedyPrefix z n ++ [false]) < z then true else false]

/-- The corresponding point of Cantor space. -/
noncomputable def greedySeq (z : ℝ) (n : ℕ) : Bool :=
  if dyadicRight (greedyPrefix z n ++ [false]) < z then true else false

theorem greedyPrefix_succ (z : ℝ) (n : ℕ) :
    greedyPrefix z (n + 1) = greedyPrefix z n ++ [greedySeq z n] := rfl

@[simp] theorem initSeg_greedySeq (z : ℝ) (n : ℕ) :
    initSeg (greedySeq z) n = greedyPrefix z n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [initSeg_succ, ih, greedyPrefix_succ]

theorem mem_dyadicInterval_greedyPrefix {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    z ∈ dyadicInterval (greedyPrefix z n) := by
  induction n with
  | zero => simpa [greedyPrefix, dyadicInterval] using hz
  | succ n ih =>
    simp only [dyadicInterval, Set.mem_Icc] at ih ⊢
    obtain ⟨hl, hr⟩ := ih
    rw [greedyPrefix_succ, greedySeq]
    by_cases hc : dyadicRight (greedyPrefix z n ++ [false]) < z
    · rw [if_pos hc]
      exact ⟨by rw [← dyadicRight_append_false_eq_left_append_true]; exact hc.le,
        by rw [dyadicRight_append_true]; exact hr⟩
    · rw [if_neg hc]
      exact ⟨by rw [dyadicLeft_append_false]; exact hl, not_lt.mp hc⟩

@[simp] theorem realOf_greedySeq {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    realOf (greedySeq z) = z :=
  (eq_realOf_of_mem_all_dyadicInterval fun n ↦ by
    rw [initSeg_greedySeq]; exact mem_dyadicInterval_greedyPrefix hz n).symm

/-- **Surjectivity onto the unit interval.** -/
theorem exists_realOf_eq {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) : ∃ x : Cantor, realOf x = z :=
  ⟨greedySeq z, realOf_greedySeq hz⟩

theorem range_realOf : Set.range realOf = Set.Icc (0 : ℝ) 1 := by
  refine Set.Subset.antisymm ?_ fun z hz ↦ ?_
  · rintro _ ⟨x, rfl⟩
    exact realOf_mem_unit x
  · obtain ⟨x, hx⟩ := exists_realOf_eq hz
    exact ⟨x, hx⟩

/-- The unit-interval-valued form, which is a genuine surjection. -/
noncomputable def realOfUnit (x : Cantor) : Set.Icc (0 : ℝ) 1 := ⟨realOf x, realOf_mem_unit x⟩

@[simp] theorem coe_realOfUnit (x : Cantor) : ((realOfUnit x : Set.Icc (0 : ℝ) 1) : ℝ) = realOf x :=
  rfl

theorem surjective_realOfUnit : Function.Surjective realOfUnit := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx⟩ := exists_realOf_eq hz
  exact ⟨x, Subtype.ext hx⟩

/-! ## Identifying a prefix from an interval

A non-rational point lies in the interior of every dyadic interval containing it, so the interval's
name *is* the point's prefix. Adjacent closed dyadic intervals share an endpoint, and that shared
endpoint is the only obstruction; non-rationality removes it. -/

theorem initSeg_eq_of_mem_dyadicInterval_of_ne_rat {x : Cantor} {σ : BitString}
    (hx : realOf x ∈ dyadicInterval σ) (hirr : ∀ q : ℚ, realOf x ≠ (q : ℝ)) :
    initSeg x σ.length = σ := by
  by_contra hne
  have hτlen : (initSeg x σ.length).length = σ.length := length_initSeg x σ.length
  have hxτ := realOf_mem_dyadicInterval x σ.length
  rw [dyadicInterval, Set.mem_Icc, dyadicLeft_eq_gridPoint, dyadicRight_eq_gridPoint_succ,
    hτlen] at hxτ
  rw [dyadicInterval, Set.mem_Icc, dyadicLeft_eq_gridPoint, dyadicRight_eq_gridPoint_succ] at hx
  have hidx : gridIndex (initSeg x σ.length) ≠ gridIndex σ := fun h ↦
    hne (gridIndex_inj_of_length hτlen h)
  have hrat : ∀ m : ℕ, ∃ q : ℚ, gridPoint σ.length m = (q : ℝ) := by
    intro m
    refine ⟨(m : ℚ) / 2 ^ σ.length, ?_⟩
    rw [gridPoint]
    push_cast
    ring
  rcases lt_or_gt_of_ne hidx with hlt | hlt
  · have hle : gridPoint σ.length (gridIndex (initSeg x σ.length) + 1)
        ≤ gridPoint σ.length (gridIndex σ) := gridPoint_le_iff.mpr hlt
    obtain ⟨q, hq⟩ := hrat (gridIndex (initSeg x σ.length) + 1)
    exact hirr q (by rw [← hq]; linarith [hx.1, hxτ.2])
  · have hle : gridPoint σ.length (gridIndex σ + 1)
        ≤ gridPoint σ.length (gridIndex (initSeg x σ.length)) := gridPoint_le_iff.mpr hlt
    obtain ⟨q, hq⟩ := hrat (gridIndex σ + 1)
    exact hirr q (by rw [← hq]; linarith [hx.2, hxτ.1])

end AlgorithmicRandomness
