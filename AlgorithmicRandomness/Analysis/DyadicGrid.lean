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

end AlgorithmicRandomness
