/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.DyadicGrid

/-!
# The cumulative function on the dyadic points of `[0, 1]`

A dyadic point of the unit interval has many names `(n, k)`, and `gridCDF_eq_of_gridPoint_eq`
says its value does not depend on which one is used. Turning that into a *function* still needs a
choice of name, so `dyadicCDF` picks one classically and the characterization theorem immediately
hides it again: no proof after this file mentions the chosen witness, and coherence is exactly
what makes the choice unobservable.

This is deliberately the semantic layer. `UnitDyadic` and `dyadicCDF` are noncomputable by
construction — a point here is a real number together with a proof that it is dyadic, and
extracting a level from that proof is classical no matter how the function is defined. The
executable content lives elsewhere and stays exact: `gridCDF` in `ℚ≥0`, and later a program in
`ComputableLipschitz.dyadicCode`. Choosing a normalized `(n, k)` carrier instead would make the
level executable, but only by reintroducing the representation bookkeeping that global coherence
exists to avoid.

The two-sided increment estimate is proved *before* the Lipschitz bound and kept as the primary
statement. The Lipschitz bound discards the lower estimate, which is the half the oscillator
argument needs.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-- A dyadic point of `[0, 1]`: a real number that occurs as a cut point of some level. -/
def UnitDyadic : Type := {x : ℝ // ∃ n k, k ≤ 2 ^ n ∧ x = gridPoint n k}

namespace UnitDyadic

instance : CoeHead UnitDyadic ℝ := ⟨Subtype.val⟩

@[ext] theorem ext {x y : UnitDyadic} (h : (x : ℝ) = (y : ℝ)) : x = y := Subtype.ext h

/-- The canonical point of level `n` and index `k`. -/
noncomputable def ofGrid (n k : ℕ) (hk : k ≤ 2 ^ n) : UnitDyadic := ⟨gridPoint n k, n, k, hk, rfl⟩

@[simp] theorem coe_ofGrid (n k : ℕ) (hk : k ≤ 2 ^ n) :
    ((ofGrid n k hk : UnitDyadic) : ℝ) = gridPoint n k := rfl

theorem mem_unit (x : UnitDyadic) : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨n, k, hk, hx⟩ := x.2
  rw [show ((x : ℝ)) = gridPoint n k from hx]
  exact gridPoint_mem_unit hk

/-- Two dyadic points can always be named at a single level. This is the only place the levels of
`x` and `y` are compared, and it is what lets every later estimate be a fixed-level one. -/
theorem exists_common_level (x y : UnitDyadic) :
    ∃ N a b, a ≤ 2 ^ N ∧ b ≤ 2 ^ N ∧ (x : ℝ) = gridPoint N a ∧ (y : ℝ) = gridPoint N b := by
  obtain ⟨n, k, hk, hx⟩ := x.2
  obtain ⟨m, l, hl, hy⟩ := y.2
  refine ⟨max n m, 2 ^ (max n m - n) * k, 2 ^ (max n m - m) * l, ?_, ?_, ?_, ?_⟩
  · calc 2 ^ (max n m - n) * k ≤ 2 ^ (max n m - n) * 2 ^ n := by gcongr
      _ = 2 ^ max n m := by rw [← pow_add]; congr 1; omega
  · calc 2 ^ (max n m - m) * l ≤ 2 ^ (max n m - m) * 2 ^ m := by gcongr
      _ = 2 ^ max n m := by rw [← pow_add]; congr 1; omega
  · rw [gridPoint_refine_of_le (le_max_left n m)]; exact hx
  · rw [gridPoint_refine_of_le (le_max_right n m)]; exact hy

end UnitDyadic

/-! ## The cumulative function -/

/-- The cumulative function at a dyadic point. The level and index are chosen classically; the
next two theorems show the choice is invisible. -/
noncomputable def dyadicCDF (M : TreeMartingale) (x : UnitDyadic) : ℝ :=
  ((gridCDF M x.2.choose x.2.choose_spec.choose : ℚ≥0) : ℝ)

/-- **The characterization.** Any name of the point computes its value, so nothing downstream
ever sees the chosen one. -/
theorem dyadicCDF_eq (M : TreeMartingale) (x : UnitDyadic) {n k : ℕ}
    (hx : (x : ℝ) = gridPoint n k) : dyadicCDF M x = ((gridCDF M n k : ℚ≥0) : ℝ) := by
  have hchosen : (x : ℝ) = gridPoint x.2.choose x.2.choose_spec.choose :=
    x.2.choose_spec.choose_spec.2
  rw [dyadicCDF, gridCDF_eq_of_gridPoint_eq M (n := x.2.choose) (m := n)
    (k := x.2.choose_spec.choose) (l := k) (by rw [← hchosen, hx])]

/-- The same at a canonical point, which is the form most call sites want. -/
@[simp] theorem dyadicCDF_eq_gridCDF (M : TreeMartingale) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    dyadicCDF M (UnitDyadic.ofGrid n k hk) = ((gridCDF M n k : ℚ≥0) : ℝ) :=
  dyadicCDF_eq M _ rfl

@[simp] theorem dyadicCDF_zero (M : TreeMartingale) :
    dyadicCDF M (UnitDyadic.ofGrid 0 0 (by norm_num)) = 0 := by
  rw [dyadicCDF_eq_gridCDF, gridCDF_zero]
  norm_num

/-! ## The two-sided estimate

The fixed-level estimate lifts verbatim once both points are named at a common level. Keeping the
lower bound is what makes this usable for the oscillator, where the point is that the chord slope
stays *above* a positive constant as well as below `K`. -/

/-- **The two-sided increment estimate on dyadic points.** -/
theorem dyadicCDF_increment_bounds (M : TreeMartingale) {c K : ℚ≥0}
    (hc : ∀ σ, c ≤ M.capital σ) (hK : ∀ σ, M.capital σ ≤ K)
    {x y : UnitDyadic} (hxy : (x : ℝ) ≤ (y : ℝ)) :
    (c : ℝ) * ((y : ℝ) - (x : ℝ)) ≤ dyadicCDF M y - dyadicCDF M x ∧
      dyadicCDF M y - dyadicCDF M x ≤ (K : ℝ) * ((y : ℝ) - (x : ℝ)) := by
  obtain ⟨N, a, b, ha, hb, hxa, hyb⟩ := UnitDyadic.exists_common_level x y
  have hab : a ≤ b := gridPoint_le_iff.mp (by rw [← hxa, ← hyb]; exact hxy)
  rw [dyadicCDF_eq M x hxa, dyadicCDF_eq M y hyb,
    show ((y : ℝ)) - (x : ℝ) = gridPoint N b - gridPoint N a by rw [hxa, hyb]]
  exact gridCDF_increment_bounds M N hc hK hab hb

/-- The Lipschitz bound, by splitting on the order of the two points. -/
theorem dyadicCDF_lipschitz (M : TreeMartingale) {K : ℚ≥0} (hK : ∀ σ, M.capital σ ≤ K)
    (x y : UnitDyadic) :
    |dyadicCDF M x - dyadicCDF M y| ≤ (K : ℝ) * |(x : ℝ) - (y : ℝ)| := by
  rcases le_total ((x : ℝ)) ((y : ℝ)) with h | h
  · obtain ⟨hlo, hhi⟩ := dyadicCDF_increment_bounds M (c := 0) (fun _ ↦ zero_le) hK h
    rw [NNRat.cast_zero, zero_mul] at hlo
    rw [abs_sub_comm (dyadicCDF M x), abs_of_nonneg (by linarith),
      abs_sub_comm ((x : ℝ)), abs_of_nonneg (by linarith)]
    exact hhi
  · obtain ⟨hlo, hhi⟩ := dyadicCDF_increment_bounds M (c := 0) (fun _ ↦ zero_le) hK h
    rw [NNRat.cast_zero, zero_mul] at hlo
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ dyadicCDF M x - dyadicCDF M y),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (x : ℝ) - (y : ℝ))]
    exact hhi

/-- Monotonicity, the `c = 0` half — every capital is nonnegative, so the cumulative function is
nondecreasing without any hypothesis. -/
theorem dyadicCDF_mono (M : TreeMartingale) {x y : UnitDyadic} (hxy : (x : ℝ) ≤ (y : ℝ)) :
    dyadicCDF M x ≤ dyadicCDF M y := by
  obtain ⟨N, a, b, ha, hb, hxa, hyb⟩ := UnitDyadic.exists_common_level x y
  have hab : a ≤ b := gridPoint_le_iff.mp (by rw [← hxa, ← hyb]; exact hxy)
  rw [dyadicCDF_eq M x hxa, dyadicCDF_eq M y hyb, NNRat.cast_le]
  rw [gridCDF_add_slice M N hab]
  exact le_add_right (le_refl _)

end AlgorithmicRandomness
