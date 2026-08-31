/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.CDFProgram
import Mathlib.LinearAlgebra.AffineSpace.Slope
import AlgorithmicRandomness.Analysis.ComputableMonotone
import AlgorithmicRandomness.Martingale.Savings
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Effective atomlessness from savings

A martingale with savings gains at most one unit per bit, so the mass it assigns to a level-`n`
cell is at most `2⁻ⁿ (M ∅ + n)`. That quantity tends to zero, which is the effective atomlessness
modulus: it bounds, uniformly in the cell, how much mass a single cell can carry, and hence how far
the cumulative function can move across one.

The boundary between exact and approximate is drawn here. The *search* for a level fine enough for
a requested precision is a comparison of coded rationals and stays in `ℚ≥0`; only its *termination*
is proved in `ℝ`, where the pinned mathlib supplies the linear-versus-geometric decay
`tendsto_self_mul_const_pow_of_lt_one`. Rebuilding that decay over `ℚ≥0` would be work with no
payoff, since the certificate is never executed.
-/

open scoped NNRat

open Filter

namespace AlgorithmicRandomness

variable {M : TreeMartingale}

/-- The uniform bound on the mass of a level-`n` cell. -/
def cellBound (M : TreeMartingale) (n : ℕ) : ℚ≥0 :=
  (2⁻¹ : ℚ≥0) ^ n * (M.capital [] + n)

/-- **The effective cell estimate.** With savings, no cell of level `n` carries more mass than
`cellBound M n`, whatever the string. -/
theorem cellMass_le (hs : M.SavingsProperty) (σ : BitString) :
    (2⁻¹ : ℚ≥0) ^ σ.length * M.capital σ ≤ cellBound M σ.length :=
  mul_le_mul_of_nonneg_left (hs.capital_le_root_add_length σ) zero_le

/-- The termination certificate, in `ℝ`: a constant times a geometric sequence plus a linear one. -/
private theorem tendsto_coe_cellBound_zero (M : TreeMartingale) :
    Tendsto (fun n ↦ ((cellBound M n : ℚ≥0) : ℝ)) atTop (nhds 0) := by
  have hgeom : Tendsto (fun n : ℕ ↦ ((M.capital [] : ℚ≥0) : ℝ) * (2⁻¹ : ℝ) ^ n) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)
    simpa using h.const_mul (((M.capital [] : ℚ≥0) : ℝ))
  have hlin : Tendsto (fun n : ℕ ↦ (n : ℝ) * (2⁻¹ : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hsum := hgeom.add hlin
  rw [add_zero] at hsum
  refine hsum.congr fun n ↦ ?_
  rw [cellBound]
  push_cast
  ring

/-- **The selector's contract.** Some level is fine enough for any requested precision. The search
itself is a comparison of coded rationals; only this proof passes through the reals. -/
theorem exists_cellBound_le (M : TreeMartingale) (k : ℕ) :
    ∃ n, cellBound M n ≤ (2⁻¹ : ℚ≥0) ^ k := by
  have hpos : (0 : ℝ) < ((2⁻¹ : ℚ≥0) ^ k : ℚ≥0) := by positivity
  have hev := (tendsto_coe_cellBound_zero M).eventually (gt_mem_nhds hpos)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, le_of_lt (by exact_mod_cast hn)⟩

/-! ## The cumulative function at a rational

The value at `q` is the supremum of the dyadic values at or below `q`. Nothing here chooses a
level: the level appears only in the executable approximation, and the two are connected by the
sandwich below. Past `1` the function is automatically constant, since every dyadic point of the
unit interval is at most `1`. -/

private theorem nonempty_cdfIndex (q : ℚ≥0) :
    Nonempty {x : UnitDyadic // (x : ℝ) ≤ ((q : ℚ) : ℝ)} := by
  refine ⟨⟨UnitDyadic.ofGrid 0 0 (by norm_num), ?_⟩⟩
  rw [UnitDyadic.coe_ofGrid, gridPoint]
  simp only [Nat.cast_zero, zero_div]
  positivity

private theorem bddAbove_cdfIndex (M : TreeMartingale) (q : ℚ≥0) :
    BddAbove (Set.range fun x : {x : UnitDyadic // (x : ℝ) ≤ ((q : ℚ) : ℝ)} ↦ dyadicCDF M x) := by
  refine ⟨dyadicCDF M (UnitDyadic.ofGrid 0 1 (by norm_num)), ?_⟩
  rintro _ ⟨x, rfl⟩
  refine dyadicCDF_mono M ?_
  rw [UnitDyadic.coe_ofGrid, gridPoint]
  simpa using (UnitDyadic.mem_unit (x : UnitDyadic)).2

/-- The cumulative function evaluated at a nonnegative rational. -/
noncomputable def cdfRat (M : TreeMartingale) (q : ℚ≥0) : ℝ :=
  ⨆ x : {x : UnitDyadic // (x : ℝ) ≤ ((q : ℚ) : ℝ)}, dyadicCDF M x

theorem monotone_cdfRat (M : TreeMartingale) : Monotone (cdfRat M) := by
  intro q q' hq
  haveI := nonempty_cdfIndex q
  haveI := nonempty_cdfIndex q'
  refine ciSup_le fun x ↦ le_ciSup_of_le (bddAbove_cdfIndex M q')
    ⟨(x : UnitDyadic), le_trans x.2 ?_⟩ le_rfl
  exact_mod_cast hq

/-- **Exactness at a cut point.** -/
theorem cdfRat_gridPoint (M : TreeMartingale) {q : ℚ≥0} {n j : ℕ} (hj : j ≤ 2 ^ n)
    (hq : ((q : ℚ) : ℝ) = gridPoint n j) :
    cdfRat M q = ((gridCDF M n j : ℚ≥0) : ℝ) := by
  haveI := nonempty_cdfIndex q
  rw [← dyadicCDF_eq_gridCDF M hj]
  refine le_antisymm (ciSup_le fun x ↦ dyadicCDF_mono M ?_)
    (le_ciSup_of_le (bddAbove_cdfIndex M q) ⟨UnitDyadic.ofGrid n j hj, ?_⟩ le_rfl)
  · rw [UnitDyadic.coe_ofGrid, ← hq]
    exact x.2
  · rw [UnitDyadic.coe_ofGrid, hq]

/-- **The one-cell sandwich.** -/
private theorem gridCDF_le_cdfRat_le_succ (M : TreeMartingale) {q : ℚ≥0} {n j : ℕ}
    (hj : j < 2 ^ n) (hlo : gridPoint n j ≤ ((q : ℚ) : ℝ))
    (hhi : ((q : ℚ) : ℝ) ≤ gridPoint n (j + 1)) :
    ((gridCDF M n j : ℚ≥0) : ℝ) ≤ cdfRat M q ∧
      cdfRat M q ≤ ((gridCDF M n (j + 1) : ℚ≥0) : ℝ) := by
  haveI := nonempty_cdfIndex q
  constructor
  · rw [← dyadicCDF_eq_gridCDF M hj.le]
    refine le_ciSup_of_le (bddAbove_cdfIndex M q) ⟨UnitDyadic.ofGrid n j hj.le, ?_⟩ le_rfl
    rw [UnitDyadic.coe_ofGrid]
    exact hlo
  · rw [← dyadicCDF_eq_gridCDF M (n := n) (k := j + 1) hj]
    refine ciSup_le fun x ↦ dyadicCDF_mono M ?_
    rw [UnitDyadic.coe_ofGrid]
    exact le_trans x.2 hhi

/-- The successor step at a cut point, with its cell named. -/
private theorem gridCDF_succ_index (M : TreeMartingale) {n j : ℕ} (hj : j < 2 ^ n) :
    gridCDF M n (j + 1)
      = gridCDF M n j + (2⁻¹ : ℚ≥0) ^ n * M.capital ((BitString.wordsOfLength n).getD j []) := by
  have hlt : j < (BitString.wordsOfLength n).length := by
    rw [BitString.length_wordsOfLength]; exact hj
  have hmem : (BitString.wordsOfLength n).getD j [] ∈ BitString.wordsOfLength n := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem _
  have hlen : ((BitString.wordsOfLength n).getD j []).length = n :=
    BitString.length_of_mem_wordsOfLength hmem
  have hidx : gridIndex ((BitString.wordsOfLength n).getD j []) = j :=
    gridIndex_getD_wordsOfLength hj
  have hsucc := gridCDF_succ M ((BitString.wordsOfLength n).getD j [])
  rwa [hlen, hidx] at hsucc

/-- One cell moves the grid value by at most the cell bound. -/
private theorem gridCDF_succ_le {M : TreeMartingale} (hs : M.SavingsProperty) {n j : ℕ}
    (hj : j < 2 ^ n) : gridCDF M n (j + 1) ≤ gridCDF M n j + cellBound M n := by
  have hlt : j < (BitString.wordsOfLength n).length := by
    rw [BitString.length_wordsOfLength]; exact hj
  have hmem : (BitString.wordsOfLength n).getD j [] ∈ BitString.wordsOfLength n := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem _
  have hlen : ((BitString.wordsOfLength n).getD j []).length = n :=
    BitString.length_of_mem_wordsOfLength hmem
  have hcell := cellMass_le hs ((BitString.wordsOfLength n).getD j [])
  rw [hlen] at hcell
  rw [gridCDF_succ_index M hj]
  exact add_le_add le_rfl hcell

/-- **The savings error bound.** Across one cell the cumulative function moves by at most the cell
mass, which savings bounds uniformly. -/
private theorem cdfRat_sub_gridCDF_le {M : TreeMartingale} (hs : M.SavingsProperty) {q : ℚ≥0}
    {n j : ℕ} (hj : j < 2 ^ n) (hlo : gridPoint n j ≤ ((q : ℚ) : ℝ))
    (hhi : ((q : ℚ) : ℝ) ≤ gridPoint n (j + 1)) :
    |cdfRat M q - ((gridCDF M n j : ℚ≥0) : ℝ)| ≤ ((cellBound M n : ℚ≥0) : ℝ) := by
  obtain ⟨h1, h2⟩ := gridCDF_le_cdfRat_le_succ M hj hlo hhi
  have hstep : ((gridCDF M n (j + 1) : ℚ≥0) : ℝ)
      ≤ ((gridCDF M n j : ℚ≥0) : ℝ) + ((cellBound M n : ℚ≥0) : ℝ) := by
    have h := gridCDF_succ_le hs hj
    exact_mod_cast h
  rw [abs_of_nonneg (by linarith)]
  linarith

/-! ## The extension to the unit interval

`supExtend (cdfRat M)` is a supremum over rationals of a supremum over dyadics; it collapses to the
supremum over dyadics, because a dyadic point below `x` is itself a rational below `x`. Turning a
`UnitDyadic` witness into that rational is the one step that is mathematical rather than
definitional, since the subtype stores only a real together with an existential grid name. -/

private theorem exists_nnrat_coe_eq (d : UnitDyadic) : ∃ q : ℚ≥0, ((q : ℚ) : ℝ) = (d : ℝ) := by
  obtain ⟨n, k, hk, hd⟩ := d.2
  refine ⟨(k : ℚ≥0) / (2 ^ n : ℚ≥0), ?_⟩
  rw [hd, gridPoint]
  push_cast
  ring

theorem supExtend_cdfRat_eq (M : TreeMartingale) (x : Set.Icc (0 : ℝ) 1) :
    supExtend (cdfRat M) x = ⨆ d : {d : UnitDyadic // (d : ℝ) ≤ (x : ℝ)}, dyadicCDF M d := by
  haveI : Nonempty {d : UnitDyadic // (d : ℝ) ≤ (x : ℝ)} := by
    refine ⟨⟨UnitDyadic.ofGrid 0 0 (by norm_num), ?_⟩⟩
    rw [UnitDyadic.coe_ofGrid, gridPoint]
    simp only [Nat.cast_zero, zero_div]
    exact x.2.1
  have hbdd : BddAbove
      (Set.range fun d : {d : UnitDyadic // (d : ℝ) ≤ (x : ℝ)} ↦ dyadicCDF M d) := by
    refine ⟨dyadicCDF M (UnitDyadic.ofGrid 0 1 (by norm_num)), ?_⟩
    rintro _ ⟨d, rfl⟩
    refine dyadicCDF_mono M ?_
    rw [UnitDyadic.coe_ofGrid, gridPoint]
    simpa using (UnitDyadic.mem_unit (d : UnitDyadic)).2
  haveI := nonempty_supExtend_index x
  refine le_antisymm (ciSup_le fun q ↦ ?_) (ciSup_le fun d ↦ ?_)
  · haveI := nonempty_cdfIndex (q : ℚ≥0)
    refine ciSup_le fun e ↦ le_ciSup_of_le hbdd ⟨(e : UnitDyadic), le_trans e.2 q.2⟩ le_rfl
  · obtain ⟨q, hq⟩ := exists_nnrat_coe_eq (d : UnitDyadic)
    refine le_ciSup_of_le (bddAbove_supExtend_index (monotone_cdfRat M) x)
      ⟨q, by rw [hq]; exact d.2⟩ ?_
    haveI := nonempty_cdfIndex q
    exact le_ciSup_of_le (bddAbove_cdfIndex M q) ⟨(d : UnitDyadic), le_of_eq hq.symm⟩ le_rfl

/-! ## The bracket at an arbitrary real, and the two-cell oscillation -/

private theorem gridCDF_le_supExtend (M : TreeMartingale) {x : Set.Icc (0 : ℝ) 1} {n j : ℕ}
    (hj : j ≤ 2 ^ n) (hlo : gridPoint n j ≤ (x : ℝ)) :
    ((gridCDF M n j : ℚ≥0) : ℝ) ≤ supExtend (cdfRat M) x := by
  rw [supExtend_cdfRat_eq, ← dyadicCDF_eq_gridCDF M hj]
  haveI : Nonempty {d : UnitDyadic // (d : ℝ) ≤ (x : ℝ)} := ⟨⟨UnitDyadic.ofGrid n j hj, hlo⟩⟩
  refine le_ciSup_of_le ?_ ⟨UnitDyadic.ofGrid n j hj, hlo⟩ le_rfl
  refine ⟨dyadicCDF M (UnitDyadic.ofGrid 0 1 (by norm_num)), ?_⟩
  rintro _ ⟨d, rfl⟩
  refine dyadicCDF_mono M ?_
  rw [UnitDyadic.coe_ofGrid, gridPoint]
  simpa using (UnitDyadic.mem_unit (d : UnitDyadic)).2

private theorem supExtend_le_gridCDF (M : TreeMartingale) {x : Set.Icc (0 : ℝ) 1} {n j : ℕ}
    (hj : j ≤ 2 ^ n) (hhi : (x : ℝ) ≤ gridPoint n j) :
    supExtend (cdfRat M) x ≤ ((gridCDF M n j : ℚ≥0) : ℝ) := by
  rw [supExtend_cdfRat_eq, ← dyadicCDF_eq_gridCDF M hj]
  haveI : Nonempty {d : UnitDyadic // (d : ℝ) ≤ (x : ℝ)} := by
    refine ⟨⟨UnitDyadic.ofGrid 0 0 (by norm_num), ?_⟩⟩
    rw [UnitDyadic.coe_ofGrid, gridPoint]
    simp only [Nat.cast_zero, zero_div]
    exact x.2.1
  refine ciSup_le fun d ↦ dyadicCDF_mono M ?_
  rw [UnitDyadic.coe_ofGrid]
  exact le_trans d.2 hhi

private theorem gridCDF_le_add_cellBound {M : TreeMartingale} (hs : M.SavingsProperty) (n j : ℕ) :
    ∀ i : ℕ, j + i ≤ 2 ^ n →
      gridCDF M n (j + i) ≤ gridCDF M n j + (i : ℚ≥0) * cellBound M n := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro h
    have hlt : j + i < 2 ^ n := by omega
    calc gridCDF M n (j + (i + 1)) = gridCDF M n ((j + i) + 1) := by ring_nf
      _ ≤ gridCDF M n (j + i) + cellBound M n := gridCDF_succ_le hs hlt
      _ ≤ (gridCDF M n j + (i : ℚ≥0) * cellBound M n) + cellBound M n :=
          add_le_add (ih (by omega)) le_rfl
      _ = gridCDF M n j + ((i : ℚ≥0) + 1) * cellBound M n := by ring
      _ = gridCDF M n j + ((i + 1 : ℕ) : ℚ≥0) * cellBound M n := by push_cast; ring

/-- **Two-cell oscillation.** Points within one cell width have cumulative values within two cell
masses: the two brackets share a cell or are adjacent. -/
private theorem supExtend_cdfRat_oscillation {M : TreeMartingale} (hs : M.SavingsProperty) (n : ℕ)
    {x y : Set.Icc (0 : ℝ) 1} (hd : (y : ℝ) - (x : ℝ) ≤ (2⁻¹ : ℝ) ^ n) :
    supExtend (cdfRat M) y - supExtend (cdfRat M) x ≤ 2 * ((cellBound M n : ℚ≥0) : ℝ) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hinv : (2⁻¹ : ℝ) ^ n = 1 / 2 ^ n := by rw [inv_pow, one_div]
  set j : ℕ := ⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊ with hjdef
  have hx0 : (0 : ℝ) ≤ (2 : ℝ) ^ n * (x : ℝ) := by
    have := x.2.1
    positivity
  have hjle : ((j : ℕ) : ℝ) ≤ (2 : ℝ) ^ n * (x : ℝ) := Nat.floor_le hx0
  have hjlt : (2 : ℝ) ^ n * (x : ℝ) < ((j : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjbound : j ≤ 2 ^ n := by
    have h : ((j : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      refine le_trans hjle ?_
      push_cast
      nlinarith [x.2.2, hpow]
    exact_mod_cast h
  set m : ℕ := min (j + 2) (2 ^ n) with hmdef
  have hmle : m ≤ 2 ^ n := min_le_right _ _
  have hjm : j ≤ m := by omega
  have hgap : m - j ≤ 2 := by omega
  have hlo : gridPoint n j ≤ (x : ℝ) := by
    rw [gridPoint, div_le_iff₀ hpow]
    linarith
  have hhi : (y : ℝ) ≤ gridPoint n m := by
    rcases le_or_gt (j + 2) (2 ^ n) with hcase | hcase
    · have hm : m = j + 2 := by omega
      rw [hm, gridPoint, le_div_iff₀ hpow]
      push_cast
      rw [hinv] at hd
      have hx : (y : ℝ) ≤ (x : ℝ) + 1 / 2 ^ n := by linarith
      have : (2 : ℝ) ^ n * ((x : ℝ) + 1 / 2 ^ n) = (2 : ℝ) ^ n * (x : ℝ) + 1 := by
        field_simp
      nlinarith [hjlt]
    · have hm : m = 2 ^ n := by omega
      rw [hm, gridPoint]
      have : ((2 ^ n : ℕ) : ℝ) / 2 ^ n = 1 := by
        push_cast
        field_simp
      rw [this]
      exact y.2.2
  have hgrid : gridCDF M n m ≤ gridCDF M n j + 2 * cellBound M n := by
    have hi : j + (m - j) = m := by omega
    have h := gridCDF_le_add_cellBound hs n j (m - j) (by omega)
    rw [hi] at h
    refine le_trans h (add_le_add le_rfl ?_)
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    exact_mod_cast hgap
  have h1 := gridCDF_le_supExtend M hjbound hlo
  have h2 := supExtend_le_gridCDF M hmle hhi
  have h3 : ((gridCDF M n m : ℚ≥0) : ℝ)
      ≤ ((gridCDF M n j : ℚ≥0) : ℝ) + 2 * ((cellBound M n : ℚ≥0) : ℝ) := by
    exact_mod_cast hgrid
  linarith

/-- **Continuity.** The cell bound is a modulus: it tends to zero and controls the oscillation
across one cell width. -/
theorem continuous_supExtend_cdfRat {M : TreeMartingale} (hs : M.SavingsProperty) :
    Continuous (supExtend (cdfRat M)) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨n, hn⟩ := ((tendsto_coe_cellBound_zero M).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists
  refine ⟨(2⁻¹ : ℝ) ^ n, by positivity, fun a hab ↦ ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq] at hab
  rw [Real.dist_eq, abs_lt]
  have hosc : ∀ u v : Set.Icc (0 : ℝ) 1, (u : ℝ) ≤ (v : ℝ) → (v : ℝ) - (u : ℝ) ≤ (2⁻¹ : ℝ) ^ n →
      supExtend (cdfRat M) v - supExtend (cdfRat M) u < ε := fun u v _ hd ↦ by
    have := supExtend_cdfRat_oscillation hs n hd
    linarith
  have hmono := monotone_supExtend (monotone_cdfRat M)
  rcases le_total (a : ℝ) (b : ℝ) with hab' | hab'
  · have h1 : supExtend (cdfRat M) a ≤ supExtend (cdfRat M) b := hmono hab'
    have h2 := hosc a b hab' (by rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hab; linarith)
    constructor <;> linarith
  · have h1 : supExtend (cdfRat M) b ≤ supExtend (cdfRat M) a := hmono hab'
    have h2 := hosc b a hab' (by rw [abs_of_nonneg (by linarith)] at hab; linarith)
    constructor <;> linarith

/-! ## The coded cell bound and the level search -/

namespace ComputableMartingale

variable (M : ComputableMartingale)

/-- The coded cell bound at level `n`. -/
def cellBoundCode (n : ℕ) : ℕ :=
  NNRatCode.divPowTwo n
    (NNRatCode.add (M.program.toFun (Encodable.encode ([] : BitString))) (NNRatCode.ofNat n))

theorem value_cellBoundCode (n : ℕ) :
    NNRatCode.value (M.cellBoundCode n) = cellBound M.toTreeMartingale n := by
  rw [cellBoundCode, NNRatCode.value_divPowTwo, NNRatCode.value_add, NNRatCode.value_ofNat,
    M.eval_capital, cellBound, inv_pow, div_eq_mul_inv]
  ring

theorem primrec_cellBoundCode : Primrec M.cellBoundCode :=
  NNRatCode.primrec_divPowTwo.comp Primrec.id
    (NNRatCode.primrec_add.comp (Primrec.const _) NNRatCode.primrec_ofNat)

/-- The level test: is the cell bound already below `2⁻ᵏ`? A comparison of coded rationals. -/
def fineAt (k n : ℕ) : Bool :=
  NNRatCode.le (M.cellBoundCode n) (NNRatCode.divPowTwo k (NNRatCode.ofNat 1))

theorem fineAt_iff {k n : ℕ} :
    M.fineAt k n = true ↔ cellBound M.toTreeMartingale n ≤ (2⁻¹ : ℚ≥0) ^ k := by
  rw [fineAt, NNRatCode.le_iff, value_cellBoundCode, NNRatCode.value_divPowTwo,
    NNRatCode.value_ofNat, Nat.cast_one, inv_pow, one_div]

theorem primrec_fineAt : Primrec₂ M.fineAt :=
  NNRatCode.primrec_le.comp (M.primrec_cellBoundCode.comp Primrec.snd)
    (NNRatCode.primrec_divPowTwo.comp Primrec.fst
      (NNRatCode.primrec_ofNat.comp (Primrec.const 1)))

/-- The search for a level fine enough for the requested precision. -/
noncomputable def cdfLevelSearch (k : ℕ) : Part ℕ :=
  Nat.rfind fun n ↦ Part.some (M.fineAt k n)

theorem partrec_cdfLevelSearch : Nat.Partrec fun k ↦ M.cdfLevelSearch k :=
  Partrec.nat_iff.mp (Partrec.rfind (Computable₂.partrec₂ M.primrec_fineAt.to_comp))

theorem cdfLevelSearch_dom (k : ℕ) : (M.cdfLevelSearch k).Dom := by
  obtain ⟨n, hn⟩ := exists_cellBound_le M.toTreeMartingale k
  obtain ⟨m, hm, -⟩ := Nat.rfind_min' (p := fun n ↦ M.fineAt k n) (M.fineAt_iff.mpr hn)
  exact Part.dom_iff_mem.mpr ⟨m, hm⟩

/-- The bundled level program. -/
noncomputable def cdfLevelCode : NatFunctionCode :=
  NatFunctionCode.ofPartrecTotal M.partrec_cdfLevelSearch M.cdfLevelSearch_dom

/-- The selected level. Every semantic result below is stated against this. -/
noncomputable def cdfLevel (k : ℕ) : ℕ := M.cdfLevelCode.toFun k

theorem computable_cdfLevel : Computable M.cdfLevel := M.cdfLevelCode.computable_toFun

theorem cdfLevel_cellBound_le (k : ℕ) :
    cellBound M.toTreeMartingale (M.cdfLevel k) ≤ (2⁻¹ : ℚ≥0) ^ k := by
  have hmem : M.cdfLevel k ∈ M.cdfLevelSearch k := by
    rw [cdfLevel, cdfLevelCode, NatFunctionCode.ofPartrecTotal_toFun]
    exact Part.get_mem _
  exact M.fineAt_iff.mp (by simpa using Nat.rfind_spec hmem)

/-! ## The approximation program

The argument is clamped into the unit interval, rounded down to a cut point of the selected level,
and the exact grid value there is returned. The error is one cell's mass, which the selected level
holds below `2⁻ᵏ`. -/

/-- On `Nat.pair q k`: the coded value at the cut point below the clamped argument. -/
noncomputable def cdfApproxFun (input : ℕ) : ℕ :=
  RatCode.ofNNRat (gridCDFCode M (M.cdfLevel input.unpair.2)
    (NNRatCode.floorScalePowTwo (M.cdfLevel input.unpair.2) (RatCode.clampUnit input.unpair.1)))

theorem computable_cdfApproxFun : Computable M.cdfApproxFun := by
  have hlevel : Computable fun input : ℕ ↦ M.cdfLevel input.unpair.2 :=
    M.computable_cdfLevel.comp (Primrec.snd.comp Primrec.unpair).to_comp
  have hindex : Computable fun input : ℕ ↦
      NNRatCode.floorScalePowTwo (M.cdfLevel input.unpair.2) (RatCode.clampUnit input.unpair.1) :=
    NNRatCode.primrec_floorScalePowTwo.to_comp.comp hlevel
      (RatCode.primrec_clampUnit.comp (Primrec.fst.comp Primrec.unpair)).to_comp
  have hpair : Computable fun input : ℕ ↦
      (M.cdfLevel input.unpair.2,
        NNRatCode.floorScalePowTwo (M.cdfLevel input.unpair.2)
          (RatCode.clampUnit input.unpair.1)) := Computable.pair hlevel hindex
  exact (RatCode.primrec_ofNNRat.to_comp.comp
    ((computable_gridCDFCode M).comp hpair)).of_eq fun _ ↦ rfl

/-- **Correctness of the approximation.** -/
theorem cdfApprox_spec (hs : M.toTreeMartingale.SavingsProperty) (q k : ℕ) :
    |cdfRat M.toTreeMartingale (NNRatCode.value (RatCode.clampUnit q))
        - ((RatCode.value (M.cdfApproxFun (Nat.pair q k)) : ℚ) : ℝ)| ≤ (2⁻¹ : ℝ) ^ k := by
  set n := M.cdfLevel k with hn
  set c : ℚ≥0 := NNRatCode.value (RatCode.clampUnit q) with hc
  set j : ℕ := NNRatCode.floorScalePowTwo n (RatCode.clampUnit q) with hjdef
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hc1 : c ≤ 1 := by
    have h := RatCode.value_clampUnit q
    have : ((c : ℚ)) ≤ 1 := by rw [hc, h]; exact max_le (by norm_num) (min_le_left _ _)
    exact_mod_cast this
  have hfloor_le : ((j : ℕ) : ℚ≥0) ≤ c * 2 ^ n :=
    NNRatCode.floorScalePowTwo_le n (RatCode.clampUnit q)
  have hfloor_lt : c * 2 ^ n < ((j : ℕ) : ℚ≥0) + 1 :=
    NNRatCode.lt_floorScalePowTwo_add_one n (RatCode.clampUnit q)
  have hjle : j ≤ 2 ^ n := by
    have h : ((j : ℕ) : ℚ≥0) ≤ 2 ^ n := by
      refine le_trans hfloor_le ?_
      calc c * 2 ^ n ≤ 1 * 2 ^ n := by gcongr
        _ = 2 ^ n := one_mul _
    exact_mod_cast h
  have hleR : ((j : ℕ) : ℝ) ≤ ((c : ℚ) : ℝ) * 2 ^ n := by exact_mod_cast hfloor_le
  have hltR : ((c : ℚ) : ℝ) * 2 ^ n < ((j : ℕ) : ℝ) + 1 := by exact_mod_cast hfloor_lt
  have hvalue : ((RatCode.value (M.cdfApproxFun (Nat.pair q k)) : ℚ) : ℝ)
      = ((gridCDF M.toTreeMartingale n j : ℚ≥0) : ℝ) := by
    rw [cdfApproxFun, Nat.unpair_pair, RatCode.value_ofNNRat, ← hn, ← hjdef,
      value_gridCDFCode M hjle]
    norm_cast
  rw [hvalue]
  rcases lt_or_eq_of_le hjle with hjlt | hjeq
  · have hlo : gridPoint n j ≤ ((c : ℚ) : ℝ) := by
      rw [gridPoint, div_le_iff₀ hpow]
      exact hleR
    have hhi : ((c : ℚ) : ℝ) ≤ gridPoint n (j + 1) := by
      rw [gridPoint, le_div_iff₀ hpow]
      push_cast at hltR ⊢
      linarith
    refine le_trans (cdfRat_sub_gridCDF_le hs hjlt hlo hhi) ?_
    have := M.cdfLevel_cellBound_le k
    rw [← hn] at this
    have hcast : ((cellBound M.toTreeMartingale n : ℚ≥0) : ℝ) ≤ (((2⁻¹ : ℚ≥0) ^ k : ℚ≥0) : ℝ) := by
      exact_mod_cast this
    refine le_trans hcast (le_of_eq ?_)
    push_cast
    ring
  · have hc_eq : ((c : ℚ) : ℝ) = gridPoint n j := by
      rw [gridPoint, eq_div_iff (ne_of_gt hpow)]
      have h1 : ((j : ℕ) : ℝ) ≤ ((c : ℚ) : ℝ) * 2 ^ n := hleR
      have h2 : ((c : ℚ) : ℝ) * 2 ^ n ≤ ((j : ℕ) : ℝ) := by
        have hc1R : ((c : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hc1
        rw [hjeq]
        push_cast at hc1R ⊢
        nlinarith
      linarith
    rw [cdfRat_gridPoint M.toTreeMartingale hjle hc_eq, sub_self, abs_zero]
    positivity

/-! ## The bundle

Everything the presentation needs is now available: the extension is monotone by inclusion of
index families, continuous by the cell bound, and approximated at every rational by the coded
program. -/

/-- **The savings CDF.** A computable martingale with savings has a computable nondecreasing
cumulative function. -/
noncomputable def toComputableMonotoneCDF (hs : M.toTreeMartingale.SavingsProperty) :
    ComputableMonotone :=
  ofRationalValues (cdfRat M.toTreeMartingale) (monotone_cdfRat _)
    (continuous_supExtend_cdfRat hs) (NatFunctionCode.ofComputable M.computable_cdfApproxFun)
    fun q k ↦ by
      rw [NatFunctionCode.apply₂, NatFunctionCode.ofComputable_toFun]
      exact M.cdfApprox_spec hs q k

@[simp] theorem toComputableMonotoneCDF_unitFun (hs : M.toTreeMartingale.SavingsProperty) :
    (M.toComputableMonotoneCDF hs).unitFun = supExtend (cdfRat M.toTreeMartingale) := rfl

/-- **Agreement at the cut points.** The bundled function is the cumulative sum exactly, which is
what the slope estimates consume. -/
theorem toComputableMonotoneCDF_gridPoint (hs : M.toTreeMartingale.SavingsProperty) {n j : ℕ}
    (hj : j ≤ 2 ^ n) :
    (M.toComputableMonotoneCDF hs).toFun (gridPoint n j)
      = ((gridCDF M.toTreeMartingale n j : ℚ≥0) : ℝ) := by
  rw [ComputableMonotone.toFun_of_mem _ (gridPoint_mem_unit hj), toComputableMonotoneCDF_unitFun]
  exact le_antisymm (supExtend_le_gridCDF _ hj (le_refl _))
    (gridCDF_le_supExtend _ hj (le_refl _))

/-- **The mathematical contract.** The chord slope of the cumulative function across a dyadic cell
is the capital there, exactly. -/
theorem toComputableMonotoneCDF_slope (hs : M.toTreeMartingale.SavingsProperty) (σ : BitString) :
    slope (M.toComputableMonotoneCDF hs).toFun (dyadicLeft σ) (dyadicRight σ)
      = ((M.capital σ : ℚ≥0) : ℝ) := by
  have hidx : gridIndex σ < 2 ^ σ.length := gridIndex_lt_two_pow σ
  have hleft : (M.toComputableMonotoneCDF hs).toFun (dyadicLeft σ)
      = ((gridCDF M.toTreeMartingale σ.length (gridIndex σ) : ℚ≥0) : ℝ) := by
    rw [dyadicLeft_eq_gridPoint, M.toComputableMonotoneCDF_gridPoint hs hidx.le]
  have hright : (M.toComputableMonotoneCDF hs).toFun (dyadicRight σ)
      = ((gridCDF M.toTreeMartingale σ.length (gridIndex σ + 1) : ℚ≥0) : ℝ) := by
    rw [dyadicRight_eq_gridPoint_succ, M.toComputableMonotoneCDF_gridPoint hs hidx]
  rw [slope_def_field, hleft, hright, ← cdfLeft_eq_gridCDF, ← cdfRight_eq_gridCDF]
  exact cdf_slope M.toTreeMartingale σ

end ComputableMartingale

end AlgorithmicRandomness
