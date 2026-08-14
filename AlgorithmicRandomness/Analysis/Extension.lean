/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.Lipschitz
import AlgorithmicRandomness.Analysis.UnitDyadic

/-!
# Extending the cumulative function off the dyadic points

The cumulative function is determined on the dyadic points and Lipschitz there. Extending it is
McShane's theorem — `LipschitzOnWith.extend_real` in mathlib — rather than a density-and-limits
argument: a real-valued function that is `K`-Lipschitz on any subset extends to a `K`-Lipschitz
function on the whole space, with no completeness or density input at all.

Two things about that are worth being precise about, since both could be overclaimed.

*The extension is not canonical as a construction, but it is unique as a function on `[0, 1]*.
McShane's formula picks one extension; any other continuous function agreeing with it on the
dyadic points agrees with it everywhere on `[0, 1]`, because the dyadic points are dense there
(`dense_unitDyadic`). So the choice is as invisible as the one inside `dyadicCDF`, and for the
same kind of reason.

*Extending to `ℝ` and then restricting to `[0, 1]` is not the same as extending to `[0, 1]`.* The
`ℝ`-valued extension is used only as a means of getting the restriction; what is packaged is the
restriction, and the ambient function is then rebuilt canonically by `Set.IccExtend`. Off `[0, 1]`
the McShane values carry no information and are not claimed to.

The Lipschitz bound is carried as a natural number throughout, matching `ComputableLipschitz`.
-/

open scoped NNReal NNRat

namespace AlgorithmicRandomness

namespace UnitDyadic

/-- The dyadic points, as a subset of `ℝ`. -/
def set : Set ℝ := {x : ℝ | ∃ n k, k ≤ 2 ^ n ∧ x = gridPoint n k}

theorem mem_set_iff {x : ℝ} : x ∈ set ↔ ∃ n k, k ≤ 2 ^ n ∧ x = gridPoint n k := Iff.rfl

theorem coe_mem_set (x : UnitDyadic) : (x : ℝ) ∈ set := x.2

theorem set_subset_unit : set ⊆ Set.Icc (0 : ℝ) 1 := fun _ hx ↦ mem_unit ⟨_, hx⟩

end UnitDyadic

/-! ## The cumulative function as a partial function on `ℝ` -/

/-- `dyadicCDF` transported to a function on `ℝ`, junk off the dyadic points. This exists only so
that `LipschitzOnWith` can be stated; nothing depends on the junk value. -/
noncomputable def dyadicCDFOn (M : TreeMartingale) : ℝ → ℝ :=
  Function.extend (Subtype.val : UnitDyadic → ℝ) (dyadicCDF M) 0

@[simp] theorem dyadicCDFOn_coe (M : TreeMartingale) (x : UnitDyadic) :
    dyadicCDFOn M (x : ℝ) = dyadicCDF M x :=
  Subtype.val_injective.extend_apply _ _ _

theorem dyadicCDFOn_gridPoint (M : TreeMartingale) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    dyadicCDFOn M (gridPoint n k) = ((gridCDF M n k : ℚ≥0) : ℝ) := by
  rw [show gridPoint n k = ((UnitDyadic.ofGrid n k hk : UnitDyadic) : ℝ) from rfl,
    dyadicCDFOn_coe, dyadicCDF_eq_gridCDF]

theorem lipschitzOnWith_dyadicCDFOn (M : TreeMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) :
    LipschitzOnWith (K : ℝ≥0) (dyadicCDFOn M) UnitDyadic.set := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have h : |dyadicCDF M ⟨x, hx⟩ - dyadicCDF M ⟨y, hy⟩| ≤ ((K : ℚ≥0) : ℝ) * |x - y| := by
    simpa using dyadicCDF_lipschitz M hK ⟨x, hx⟩ ⟨y, hy⟩
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_natCast,
    show dyadicCDFOn M x = dyadicCDF M ⟨x, hx⟩ from dyadicCDFOn_coe M ⟨x, hx⟩,
    show dyadicCDFOn M y = dyadicCDF M ⟨y, hy⟩ from dyadicCDFOn_coe M ⟨y, hy⟩]
  calc |dyadicCDF M ⟨x, hx⟩ - dyadicCDF M ⟨y, hy⟩| ≤ ((K : ℚ≥0) : ℝ) * |x - y| := h
    _ = (K : ℝ) * |x - y| := by push_cast; ring

/-! ## The extension -/

/-- A `K`-Lipschitz function on all of `ℝ` agreeing with the cumulative function at every dyadic
point. Existence is McShane's theorem; the next two lemmas are its full specification, and no
later proof looks inside. -/
theorem exists_lipschitz_extension (M : TreeMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) :
    ∃ g : ℝ → ℝ, LipschitzWith (K : ℝ≥0) g ∧
      ∀ (n k : ℕ), k ≤ 2 ^ n → g (gridPoint n k) = ((gridCDF M n k : ℚ≥0) : ℝ) := by
  obtain ⟨g, hg, heq⟩ := (lipschitzOnWith_dyadicCDFOn M hK).extend_real
  refine ⟨g, hg, fun n k hk ↦ ?_⟩
  rw [← heq ⟨n, k, hk, rfl⟩, dyadicCDFOn_gridPoint M hk]

/-- The chosen extension. -/
noncomputable def cdfExtension (M : TreeMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) : ℝ → ℝ :=
  (exists_lipschitz_extension M hK).choose

theorem lipschitzWith_cdfExtension (M : TreeMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) :
    LipschitzWith (K : ℝ≥0) (cdfExtension M hK) :=
  (exists_lipschitz_extension M hK).choose_spec.1

@[simp] theorem cdfExtension_gridPoint (M : TreeMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    cdfExtension M hK (gridPoint n k) = ((gridCDF M n k : ℚ≥0) : ℝ) :=
  (exists_lipschitz_extension M hK).choose_spec.2 n k hk

/-- The restriction to the unit interval, which is the honest object: this is where the extension
is determined by the data. -/
noncomputable def unitCDF (M : TreeMartingale) {K : ℕ} (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) :
    Set.Icc (0 : ℝ) 1 → ℝ :=
  fun x ↦ cdfExtension M hK (x : ℝ)

theorem lipschitzWith_unitCDF (M : TreeMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) :
    LipschitzWith (K : ℝ≥0) (unitCDF M hK) := by
  have h := (lipschitzWith_cdfExtension M hK).comp
    (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
  rwa [mul_one] at h

@[simp] theorem unitCDF_unitGridPoint (M : TreeMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    unitCDF M hK (unitGridPoint n k hk) = ((gridCDF M n k : ℚ≥0) : ℝ) :=
  cdfExtension_gridPoint M hK hk

/-! ## Uniqueness on the unit interval

The construction chose an extension, but there was nothing to choose: the dyadic points are dense
in `[0, 1]`, so a continuous function on `[0, 1]` is determined by its values on them. This is
what licenses calling `unitCDF` *the* extension. -/

/-- Every point of `[0, 1]` is approximated by cut points: at level `n`, take the index `⌊x·2^n⌋`.
-/
theorem exists_gridPoint_close {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    ∃ k ≤ 2 ^ n, |x - gridPoint n k| ≤ (2 : ℝ)⁻¹ ^ n := by
  obtain ⟨hx0, hx1⟩ := hx
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hfl0 : (0 : ℤ) ≤ ⌊x * 2 ^ n⌋ := Int.floor_nonneg.mpr (by positivity)
  have hkc : ((⌊x * 2 ^ n⌋.toNat : ℕ) : ℝ) = (⌊x * 2 ^ n⌋ : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hfl0)
  refine ⟨⌊x * 2 ^ n⌋.toNat, ?_, ?_⟩
  · have hle : (⌊x * 2 ^ n⌋ : ℝ) ≤ 2 ^ n := (Int.floor_le _).trans (by nlinarith)
    have hfin : (⌊x * 2 ^ n⌋.toNat : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      rw [hkc]; push_cast; exact hle
    exact_mod_cast hfin
  · have ha : ((⌊x * 2 ^ n⌋.toNat : ℕ) : ℝ) / 2 ^ n ≤ x := by
      rw [hkc, div_le_iff₀ hpow]
      exact Int.floor_le _
    have hb : x ≤ (((⌊x * 2 ^ n⌋.toNat : ℕ) : ℝ) + 1) / 2 ^ n := by
      rw [hkc, le_div_iff₀ hpow]
      exact (Int.lt_floor_add_one _).le
    rw [add_div, one_div] at hb
    rw [gridPoint, abs_le, inv_pow]
    constructor <;> linarith

/-- The dyadic points are dense in the unit interval. -/
theorem dense_unitDyadic {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ UnitDyadic.set, |x - y| < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨k, hk, hclose⟩ := exists_gridPoint_close hx n
  exact ⟨gridPoint n k, ⟨n, k, hk, rfl⟩, lt_of_le_of_lt hclose hn⟩

/-- **Uniqueness**: two continuous functions on `[0, 1]` agreeing at every cut point agree. -/
theorem eqOn_of_continuousOn_of_eq_gridPoint {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (h : ∀ (n k : ℕ), k ≤ 2 ^ n → f (gridPoint n k) = g (gridPoint n k)) :
    Set.EqOn f g (Set.Icc (0 : ℝ) 1) := by
  have heq : Set.EqOn f g (UnitDyadic.set ∩ Set.Icc (0 : ℝ) 1) := by
    rintro y ⟨⟨n, k, hk, rfl⟩, -⟩
    exact h n k hk
  refine heq.of_subset_closure hf hg Set.inter_subset_right fun x hx ↦ ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, hy, hlt⟩ := dense_unitDyadic hx hε
  exact ⟨y, ⟨hy, UnitDyadic.set_subset_unit hy⟩, by rwa [Real.dist_eq]⟩

end AlgorithmicRandomness
