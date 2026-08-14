/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.Dyadic

/-!
# Fixed-level dyadic grids

At level `n` the unit interval is cut at the `2 ^ n + 1` points `k / 2 ^ n`. Taking the *cut
points* rather than the cells as primary handles `0` and `1` uniformly, and pins each dyadic
point to an integer index at that level — which is what makes global well-definedness a
comparison of integers rather than a normal-form argument about binary strings.

The cells are enumerated as a `List`, not a `Finset`: the eventual computability witness will
need to run over them, and mathlib supplies no `Primcodable (Finset _)`. `gridCDF` is kept exact
in `ℚ≥0`, with casts to `ℝ` only in semantic statements, so the executable/semantic split is
already in place rather than being retrofitted.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-! ## The level enumeration -/

/-- The level-`n` cells, in binary order. -/
def levelWords : ℕ → List BitString
  | 0 => [[]]
  | n + 1 => (levelWords n).flatMap fun σ ↦ [σ ++ [false], σ ++ [true]]

@[simp] theorem levelWords_zero : levelWords 0 = [[]] := rfl

theorem levelWords_succ (n : ℕ) :
    levelWords (n + 1) = (levelWords n).flatMap fun σ ↦ [σ ++ [false], σ ++ [true]] := rfl

/-- There are `2 ^ n` cells at level `n`. -/
@[simp] theorem length_levelWords (n : ℕ) : (levelWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [levelWords_succ, List.length_flatMap]
    simp [ih, pow_succ, Nat.mul_comm]

/-- Every level-`n` cell is named by a string of length `n`. -/
theorem length_of_mem_levelWords {n : ℕ} {σ : BitString} (h : σ ∈ levelWords n) :
    σ.length = n := by
  induction n generalizing σ with
  | zero => rw [levelWords_zero, List.mem_singleton] at h; rw [h]; rfl
  | succ n ih =>
    rw [levelWords_succ, List.mem_flatMap] at h
    obtain ⟨τ, hτ, hmem⟩ := h
    have hτn := ih hτ
    rcases List.mem_pair.mp hmem with rfl | rfl <;> simp [hτn]

/-! ## Cut points -/

/-- The `k`-th cut point at level `n`. -/
noncomputable def gridPoint (n k : ℕ) : ℝ := (k : ℝ) / 2 ^ n

@[simp] theorem gridPoint_zero (n : ℕ) : gridPoint n 0 = 0 := by rw [gridPoint]; simp

@[simp] theorem gridPoint_top (n : ℕ) : gridPoint n (2 ^ n) = 1 := by
  rw [gridPoint]
  push_cast
  field_simp

/-- Refining the level doubles the index. -/
theorem gridPoint_refine (n k : ℕ) : gridPoint (n + 1) (2 * k) = gridPoint n k := by
  rw [gridPoint, gridPoint, pow_succ]
  push_cast
  ring

theorem gridPoint_mono {n k l : ℕ} (h : k ≤ l) : gridPoint n k ≤ gridPoint n l := by
  have hk : ((k : ℝ)) ≤ (l : ℝ) := by exact_mod_cast h
  rw [gridPoint, gridPoint]
  gcongr

/-- At a fixed level the order on cut points is the order on indices, in both directions. -/
theorem gridPoint_le_iff {n k l : ℕ} : gridPoint n k ≤ gridPoint n l ↔ k ≤ l := by
  rw [gridPoint, gridPoint, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n),
    Nat.cast_le]

/-- The gap between two cut points is the index difference, scaled. -/
theorem gridPoint_sub {n k l : ℕ} (h : k ≤ l) :
    gridPoint n l - gridPoint n k = ((l - k : ℕ) : ℝ) / 2 ^ n := by
  rw [gridPoint, gridPoint, div_sub_div_same, Nat.cast_sub h]

/-! ## The cumulative function on the grid -/

/-- The cumulative value at the `k`-th cut point of level `n`: the mass of the first `k` cells.
Exact in `ℚ≥0`, and a `List` sum so that it stays executable. -/
def gridCDF (M : TreeMartingale) (n k : ℕ) : ℚ≥0 :=
  (((levelWords n).take k).map fun σ ↦ (2⁻¹ : ℚ≥0) ^ n * M.capital σ).sum

@[simp] theorem gridCDF_zero (M : TreeMartingale) (n : ℕ) : gridCDF M n 0 = 0 := by
  rw [gridCDF]; simp

/-- Splitting the prefix sum at an intermediate index. -/
theorem gridCDF_add_slice (M : TreeMartingale) (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    gridCDF M n l = gridCDF M n k
      + (((((levelWords n).drop k).take (l - k))).map fun σ ↦
          (2⁻¹ : ℚ≥0) ^ n * M.capital σ).sum := by
  rw [gridCDF, gridCDF, ← List.sum_append, ← List.map_append]
  congr 2
  rw [← List.take_append_drop k ((levelWords n).take l)]
  congr 1
  · rw [List.take_take, Nat.min_eq_left h]
  · rw [List.drop_take, List.take_drop]

/-- Taking a prefix commutes with the child expansion, since each cell contributes exactly two
children. -/
theorem take_flatMap_pair (f : BitString → List BitString)
    (hf : ∀ σ, (f σ).length = 2) (l : List BitString) (k : ℕ) :
    (l.flatMap f).take (2 * k) = (l.take k).flatMap f := by
  induction l generalizing k with
  | nil => simp
  | cons σ l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, List.flatMap_cons, List.flatMap_cons, List.take_append, hf σ]
      have h2 : 2 * (k + 1) - 2 = 2 * k := by omega
      rw [h2, ih k, List.take_of_length_le (by rw [hf σ]; omega)]

/-- **Refinement**: the same cut point at the next level carries the same value. This is exactly
fairness — each cell's two children carry its mass between them. -/
theorem gridCDF_refine (M : TreeMartingale) (n k : ℕ) :
    gridCDF M (n + 1) (2 * k) = gridCDF M n k := by
  rw [gridCDF, gridCDF, levelWords_succ,
    take_flatMap_pair _ (fun σ ↦ by simp) (levelWords n) k]
  induction ((levelWords n).take k) with
  | nil => simp
  | cons σ l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_cons, List.sum_nil, List.map_cons, List.sum_cons,
      add_zero]
    have hfair : M.capital (σ ++ [false]) + M.capital (σ ++ [true]) = 2 * M.capital σ := M.fair σ
    have hstep : (2⁻¹ : ℚ≥0) ^ (n + 1) * M.capital (σ ++ [false])
        + (2⁻¹ : ℚ≥0) ^ (n + 1) * M.capital (σ ++ [true]) = (2⁻¹ : ℚ≥0) ^ n * M.capital σ := by
      rw [← mul_add, hfair, pow_succ]
      rw [show (2⁻¹ : ℚ≥0) ^ n * 2⁻¹ * (2 * M.capital σ)
          = ((2⁻¹ : ℚ≥0) * 2) * ((2⁻¹ : ℚ≥0) ^ n * M.capital σ) by ring]
      norm_num
    rw [hstep]

/-! ## The two-sided increment estimate -/

/-- A list of reals whose entries are trapped has its sum trapped by the count. -/
private theorem sum_sandwich (l : List ℝ) (c K : ℝ) (hc : ∀ y ∈ l, c ≤ y)
    (hK : ∀ y ∈ l, y ≤ K) : (l.length : ℝ) * c ≤ l.sum ∧ l.sum ≤ (l.length : ℝ) * K := by
  induction l with
  | nil => simp
  | cons a t ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun y hy ↦ hc y (List.mem_cons_of_mem a hy))
      (fun y hy ↦ hK y (List.mem_cons_of_mem a hy))
    have h1 := hc a List.mem_cons_self
    have h2 := hK a List.mem_cons_self
    rw [List.length_cons, List.sum_cons]
    push_cast
    constructor <;> nlinarith

/-- **The two-sided increment estimate.** Under a two-sided bound on the capital, the cumulative
function's increment across a run of cells is trapped between the same multiples of the gap. -/
theorem gridCDF_increment_bounds (M : TreeMartingale) {c K : ℚ≥0} (n : ℕ)
    (hc : ∀ σ, c ≤ M.capital σ) (hK : ∀ σ, M.capital σ ≤ K) {k l : ℕ} (hkl : k ≤ l)
    (hl : l ≤ 2 ^ n) :
    (c : ℝ) * (gridPoint n l - gridPoint n k)
        ≤ ((gridCDF M n l : ℚ≥0) : ℝ) - ((gridCDF M n k : ℚ≥0) : ℝ) ∧
      ((gridCDF M n l : ℚ≥0) : ℝ) - ((gridCDF M n k : ℚ≥0) : ℝ)
        ≤ (K : ℝ) * (gridPoint n l - gridPoint n k) := by
  set L := (((levelWords n).drop k).take (l - k)).map fun σ ↦ (2⁻¹ : ℚ≥0) ^ n * M.capital σ
    with hL
  set S := L.map (fun q : ℚ≥0 ↦ (q : ℝ)) with hS
  have hlen : S.length = l - k := by
    rw [hS, hL, List.length_map, List.length_map, List.length_take, List.length_drop,
      length_levelWords]
    omega
  have hsum : (L.sum : ℝ) = S.sum := by
    rw [hS]
    induction L with
    | nil => simp
    | cons a t ih => rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]; push_cast; ring
  have hdiff : ((gridCDF M n l : ℚ≥0) : ℝ) - ((gridCDF M n k : ℚ≥0) : ℝ) = S.sum := by
    rw [gridCDF_add_slice M n hkl, ← hL, ← hsum]
    push_cast
    ring
  have hpow : ((((2⁻¹ : ℚ≥0) ^ n : ℚ≥0)) : ℝ) = 1 / 2 ^ n := by
    push_cast
    rw [inv_pow]
    ring
  have hterm : ∀ y ∈ S, (c : ℝ) / 2 ^ n ≤ y ∧ y ≤ (K : ℝ) / 2 ^ n := by
    intro y hy
    rw [hS, List.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    rw [hL, List.mem_map] at hq
    obtain ⟨σ, -, rfl⟩ := hq
    have hcσ : (c : ℝ) ≤ ((M.capital σ : ℚ≥0) : ℝ) := by exact_mod_cast hc σ
    have hKσ : ((M.capital σ : ℚ≥0) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK σ
    have hval : (((2⁻¹ : ℚ≥0) ^ n * M.capital σ : ℚ≥0) : ℝ)
        = ((M.capital σ : ℚ≥0) : ℝ) / 2 ^ n := by
      rw [NNRat.cast_mul, hpow]
      ring
    rw [hval]
    exact ⟨by gcongr, by gcongr⟩
  obtain ⟨hlo, hhi⟩ := sum_sandwich S ((c : ℝ) / 2 ^ n) ((K : ℝ) / 2 ^ n)
    (fun y hy ↦ (hterm y hy).1) (fun y hy ↦ (hterm y hy).2)
  rw [hlen] at hlo hhi
  rw [hdiff, gridPoint_sub hkl]
  constructor
  · calc (c : ℝ) * (((l - k : ℕ) : ℝ) / 2 ^ n)
        = ((l - k : ℕ) : ℝ) * ((c : ℝ) / 2 ^ n) := by ring
      _ ≤ S.sum := hlo
  · calc S.sum ≤ ((l - k : ℕ) : ℝ) * ((K : ℝ) / 2 ^ n) := hhi
      _ = (K : ℝ) * (((l - k : ℕ) : ℝ) / 2 ^ n) := by ring

/-! ## Indexing strings by their binary value -/

/-- The integer index of `σ` at level `|σ|`: the string read as a binary numeral. -/
def gridIndex (σ : BitString) : ℕ := σ.foldl (fun k b ↦ 2 * k + if b then 1 else 0) 0

@[simp] theorem gridIndex_nil : gridIndex [] = 0 := rfl

@[simp] theorem gridIndex_append_false (σ : BitString) :
    gridIndex (σ ++ [false]) = 2 * gridIndex σ := by
  rw [gridIndex, List.foldl_append, List.foldl_cons, List.foldl_nil, ← gridIndex]
  simp

@[simp] theorem gridIndex_append_true (σ : BitString) :
    gridIndex (σ ++ [true]) = 2 * gridIndex σ + 1 := by
  rw [gridIndex, List.foldl_append, List.foldl_cons, List.foldl_nil, ← gridIndex]
  simp

theorem gridIndex_lt_two_pow (σ : BitString) : gridIndex σ < 2 ^ σ.length := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b ih =>
    rw [List.length_append, List.length_singleton, pow_succ]
    cases b
    · rw [gridIndex_append_false]; omega
    · rw [gridIndex_append_true]; omega

/-- The left endpoint is the cut point at the string's own index. -/
theorem dyadicLeft_eq_gridPoint (σ : BitString) :
    dyadicLeft σ = gridPoint σ.length (gridIndex σ) := by
  induction σ using List.reverseRecOn with
  | nil => simp [gridPoint]
  | append_singleton σ b ih =>
    rw [dyadicLeft_append, ih, List.length_append, List.length_singleton, gridPoint, gridPoint,
      dyadicWidth]
    cases b
    · rw [gridIndex_append_false]
      simp only [Bool.false_eq_true, if_false]
      rw [pow_succ]
      push_cast
      ring
    · rw [gridIndex_append_true]
      simp only [if_true]
      rw [inv_pow]
      push_cast
      ring

/-- And the right endpoint is the next cut point. -/
theorem dyadicRight_eq_gridPoint_succ (σ : BitString) :
    dyadicRight σ = gridPoint σ.length (gridIndex σ + 1) := by
  rw [dyadicRight, dyadicLeft_eq_gridPoint, gridPoint, gridPoint, dyadicWidth, inv_pow]
  push_cast
  ring

/-! ## The order certificate -/

private theorem range_flatMap_pair (m : ℕ) :
    (List.range m).flatMap (fun k ↦ [2 * k, 2 * k + 1]) = List.range (2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    have h1 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h1, List.range_succ, List.range_succ]
    simp

/-- **The order certificate**: level `n` enumerates the indices `0, …, 2^n - 1` in order. This
single statement carries binary order, distinctness, and indexed lookup. -/
theorem map_gridIndex_levelWords (n : ℕ) :
    (levelWords n).map gridIndex = List.range (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [levelWords_succ, List.map_flatMap]
    have hcell : ∀ σ : BitString,
        ([σ ++ [false], σ ++ [true]]).map gridIndex = [2 * gridIndex σ, 2 * gridIndex σ + 1] := by
      intro σ; simp
    rw [List.flatMap_congr (fun σ _ ↦ hcell σ),
      show ((levelWords n).flatMap fun σ ↦ [2 * gridIndex σ, 2 * gridIndex σ + 1])
        = ((levelWords n).map gridIndex).flatMap (fun k ↦ [2 * k, 2 * k + 1]) by
        rw [List.flatMap_map], ih, range_flatMap_pair, pow_succ]
    congr 1
    omega

/-- Distinctness, an immediate consequence. -/
theorem nodup_levelWords (n : ℕ) : (levelWords n).Nodup := by
  have h := map_gridIndex_levelWords n
  exact List.Nodup.of_map gridIndex (by rw [h]; exact List.nodup_range)

/-! ## Lookup is inverse to indexing

The order certificate says the index map is a bijection onto `Fin (2 ^ n)`; these two lemmas are
that bijection stated as a pair of inverses, which is the form the endpoint bridges use. -/

/-- Every string of length `n` names a level-`n` cell. -/
theorem mem_levelWords_length (σ : BitString) : σ ∈ levelWords σ.length := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton τ b ih =>
    rw [List.length_append, List.length_singleton, levelWords_succ, List.mem_flatMap]
    exact ⟨τ, ih, by cases b <;> simp⟩

/-- At a fixed length the index determines the string. -/
theorem gridIndex_inj_of_length {σ τ : BitString} (hlen : σ.length = τ.length)
    (h : gridIndex σ = gridIndex τ) : σ = τ := by
  have hnd : ((levelWords σ.length).map gridIndex).Nodup := by
    rw [map_gridIndex_levelWords]; exact List.nodup_range
  exact List.inj_on_of_nodup_map hnd (mem_levelWords_length σ)
    (by rw [hlen]; exact mem_levelWords_length τ) h

/-- Lookup then index is the identity on indices below `2 ^ n`. -/
theorem gridIndex_getD_levelWords {n k : ℕ} (hk : k < 2 ^ n) :
    gridIndex ((levelWords n).getD k []) = k := by
  have hlen : k < (levelWords n).length := by rw [length_levelWords]; exact hk
  have h : ((levelWords n).map gridIndex).getD k 0 = (List.range (2 ^ n)).getD k 0 := by
    rw [map_gridIndex_levelWords]
  rw [List.getD_eq_getElem _ _ _, List.getElem_map, List.getD_eq_getElem _ _ _,
    List.getElem_range] at h
  · rwa [List.getD_eq_getElem _ _ _]
  · simpa using hk
  · simpa using hk

/-- Index then lookup is the identity on strings. -/
theorem getD_levelWords_gridIndex (σ : BitString) :
    (levelWords σ.length).getD (gridIndex σ) [] = σ := by
  have hk : gridIndex σ < (levelWords σ.length).length := by
    rw [length_levelWords]; exact gridIndex_lt_two_pow σ
  refine gridIndex_inj_of_length ?_ (gridIndex_getD_levelWords (gridIndex_lt_two_pow σ))
  rw [List.getD_eq_getElem (hn := hk)]
  exact length_of_mem_levelWords (List.getElem_mem hk)

/-! ## The endpoint bridges

The endpoint layer of `Dyadic.lean` and the grid layer of this file are two descriptions of the
same function; these two theorems identify them. With them, everything proved by induction on
strings transfers to the grid, where indices are integers and comparison is decidable. -/

/-- **One cell's mass.** Advancing the index by one past `σ` adds exactly `σ`'s own contribution.
This is the single computation behind both bridges. -/
theorem gridCDF_succ (M : TreeMartingale) (σ : BitString) :
    gridCDF M σ.length (gridIndex σ + 1)
      = gridCDF M σ.length (gridIndex σ) + (2⁻¹ : ℚ≥0) ^ σ.length * M.capital σ := by
  have hk : gridIndex σ < (levelWords σ.length).length := by
    rw [length_levelWords]; exact gridIndex_lt_two_pow σ
  have hσ : (levelWords σ.length)[gridIndex σ] = σ := by
    rw [← List.getD_eq_getElem (d := ([] : BitString)) (hn := hk)]
    exact getD_levelWords_gridIndex σ
  have hone : gridIndex σ + 1 - gridIndex σ = 1 := by omega
  rw [gridCDF_add_slice M σ.length (Nat.le_succ _), hone, List.drop_eq_getElem_cons hk, hσ]
  simp

/-- **The odd cut.** At the refined level the odd index sits between the two children of `σ`:
the parent's prefix sum plus the left child's mass. -/
theorem gridCDF_refine_odd (M : TreeMartingale) (σ : BitString) :
    gridCDF M (σ.length + 1) (2 * gridIndex σ + 1)
      = gridCDF M σ.length (gridIndex σ)
        + (2⁻¹ : ℚ≥0) ^ (σ.length + 1) * M.capital (σ ++ [false]) := by
  have hlen : (σ ++ [false]).length = σ.length + 1 := by simp
  have h := gridCDF_succ M (σ ++ [false])
  rw [hlen, gridIndex_append_false] at h
  rw [h, gridCDF_refine]

/-- **Left endpoint bridge**: the endpoint value at `0.σ` is the grid value at `σ`'s index. -/
theorem cdfLeft_eq_gridCDF (M : TreeMartingale) (σ : BitString) :
    cdfLeft M σ = ((gridCDF M σ.length (gridIndex σ) : ℚ≥0) : ℝ) := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b ih =>
    cases b
    · rw [cdfLeft_append_false, ih, List.length_append, List.length_singleton,
        gridIndex_append_false, gridCDF_refine]
    · rw [cdfLeft_append, if_pos rfl, ih, List.length_append, List.length_singleton,
        gridIndex_append_true, gridCDF_refine_odd, dyadicWidth, List.length_append,
        List.length_singleton]
      push_cast
      ring

/-- **Right endpoint bridge**: and the value at the far end is the grid value one index on. -/
theorem cdfRight_eq_gridCDF (M : TreeMartingale) (σ : BitString) :
    cdfRight M σ = ((gridCDF M σ.length (gridIndex σ + 1) : ℚ≥0) : ℝ) := by
  rw [cdfRight, cdfLeft_eq_gridCDF, gridCDF_succ, dyadicWidth]
  push_cast
  ring

/-! ## Iterated refinement and global coherence

Single-step refinement iterates, so any two levels can be compared at a common one. Since a cut
point determines its index at a fixed level, this makes the cumulative value depend only on the
*point* — not on the level or the index used to name it. That is the statement the dense
extension needs, and it is where the choice of cut points over cells pays off: the comparison is
between natural numbers, not between binary strings up to trailing zeros. -/

/-- Refining by `m` levels scales the index by `2 ^ m`. -/
theorem gridPoint_refine_add (n m k : ℕ) : gridPoint (n + m) (2 ^ m * k) = gridPoint n k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 ^ (m + 1) * k = 2 * (2 ^ m * k) by ring, show n + (m + 1) = n + m + 1 from rfl,
      gridPoint_refine, ih]

theorem gridCDF_refine_add (M : TreeMartingale) (n m k : ℕ) :
    gridCDF M (n + m) (2 ^ m * k) = gridCDF M n k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 ^ (m + 1) * k = 2 * (2 ^ m * k) by ring, show n + (m + 1) = n + m + 1 from rfl,
      gridCDF_refine, ih]

/-- The same, indexed by the target level — the form the common-level argument uses. -/
theorem gridPoint_refine_of_le {n m : ℕ} (h : n ≤ m) (k : ℕ) :
    gridPoint m (2 ^ (m - n) * k) = gridPoint n k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact gridPoint_refine_add n d k

theorem gridCDF_refine_of_le (M : TreeMartingale) {n m : ℕ} (h : n ≤ m) (k : ℕ) :
    gridCDF M m (2 ^ (m - n) * k) = gridCDF M n k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact gridCDF_refine_add M n d k

/-- At a fixed level the cut point determines the index. -/
theorem gridPoint_inj {n k l : ℕ} (h : gridPoint n k = gridPoint n l) : k = l := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [gridPoint, gridPoint, div_eq_div_iff h2 h2] at h
  exact_mod_cast mul_right_cancel₀ h2 h

/-- **Global coherence**: equal cut points carry equal values, whatever level and index name
them. No bound on the indices is needed — single-step refinement holds at every index, so the
argument is simply "refine the coarser level to the finer one and compare integers". -/
theorem gridCDF_eq_of_gridPoint_eq (M : TreeMartingale) {n m k l : ℕ}
    (h : gridPoint n k = gridPoint m l) : gridCDF M n k = gridCDF M m l := by
  rcases le_total n m with hnm | hmn
  · have hk : gridPoint m (2 ^ (m - n) * k) = gridPoint m l := by
      rw [gridPoint_refine_of_le hnm]; exact h
    rw [← gridCDF_refine_of_le M hnm k, gridPoint_inj hk]
  · symm
    have hl : gridPoint n (2 ^ (n - m) * l) = gridPoint n k := by
      rw [gridPoint_refine_of_le hmn]; exact h.symm
    rw [← gridCDF_refine_of_le M hmn l, gridPoint_inj hl]

/-- The bounded restatement, for callers that carry unit-interval indices anyway. -/
theorem gridCDF_eq_of_gridPoint_eq_of_le (M : TreeMartingale) {n m k l : ℕ}
    (_hk : k ≤ 2 ^ n) (_hl : l ≤ 2 ^ m) (h : gridPoint n k = gridPoint m l) :
    gridCDF M n k = gridCDF M m l :=
  gridCDF_eq_of_gridPoint_eq M h

/-! ## Cut points as points of the unit interval -/

theorem gridPoint_mem_unit {n k : ℕ} (hk : k ≤ 2 ^ n) : gridPoint n k ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by rw [gridPoint]; positivity, ?_⟩
  rw [gridPoint, div_le_one (by positivity)]
  exact_mod_cast hk

/-- A cut point of the unit grid, as an element of `Icc 0 1`. This is the domain on which the
cumulative function is genuinely defined; everything outside is a matter of extension. -/
noncomputable def unitGridPoint (n k : ℕ) (hk : k ≤ 2 ^ n) : Set.Icc (0 : ℝ) 1 :=
  ⟨gridPoint n k, gridPoint_mem_unit hk⟩

@[simp] theorem unitGridPoint_coe (n k : ℕ) (hk : k ≤ 2 ^ n) :
    ((unitGridPoint n k hk : Set.Icc (0 : ℝ) 1) : ℝ) = gridPoint n k := rfl

end AlgorithmicRandomness
