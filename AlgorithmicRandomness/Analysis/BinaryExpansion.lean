/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.Dyadic

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

end AlgorithmicRandomness
