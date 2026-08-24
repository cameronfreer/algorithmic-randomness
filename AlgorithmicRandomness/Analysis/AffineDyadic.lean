/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.DyadicGrid
import AlgorithmicRandomness.Coding.RatCode
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# Rationally scaled and shifted dyadic grids

The dyadic grid is too rigid for BMN's argument: an interval with irrational endpoints need not sit
inside a dyadic interval of comparable length. Rescaling by a positive rational `p` and shifting by
a rational `q` gives a family of grids that, taken finitely many at a time, does approximate every
interior interval from both sides.

*The codes are primary.* A grid is a pair of coded rationals plus positivity of the scale; the real
scale and shift are projections. Everything a program needs is then finite data, and the semantic
endpoints are defined separately and connected by bridge theorems, as everywhere else here.

*Endpoints are computed by a fold carrying `(left, width)`, not through a grid index.* The fold
follows the tree direction directly, uses only `RatCode.half` and `RatCode.add`, and is primitive
recursive by `List.foldl`. Recovering an endpoint from an index would need the string read as a
binary numeral and a division, for no gain.

The two slope facts at the end are the algebra the martingale construction consumes: the children's
slopes average to the parent's, and monotone functions have nonnegative slopes. The martingale
itself is deliberately not built here.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-- A dyadic grid rescaled by a positive rational and shifted by a rational, presented by codes. -/
structure AffineDyadicGrid where
  /-- The scale, as a coded nonnegative rational. -/
  scaleCode : ℕ
  /-- The shift, as a coded signed rational. -/
  shiftCode : ℕ
  /-- The scale is positive, so the grid is a genuine rescaling. -/
  scale_pos : 0 < NNRatCode.value scaleCode

namespace AffineDyadicGrid

variable (G : AffineDyadicGrid)

/-! ## The real parameters -/

/-- The scale as a real. -/
noncomputable def scale : ℝ := ((NNRatCode.value G.scaleCode : ℚ) : ℝ)

/-- The shift as a real. -/
noncomputable def shift : ℝ := ((RatCode.value G.shiftCode : ℚ) : ℝ)

theorem zero_lt_scale : 0 < G.scale := by
  rw [scale]
  exact_mod_cast G.scale_pos

/-! ## Semantic endpoints -/

/-- The left endpoint of the affine interval named by `σ`. -/
noncomputable def left (σ : BitString) : ℝ := G.scale * dyadicLeft σ + G.shift

/-- Its width. -/
noncomputable def width (σ : BitString) : ℝ := G.scale * dyadicWidth σ

/-- Its right endpoint. -/
noncomputable def right (σ : BitString) : ℝ := G.left σ + G.width σ

/-- The interval itself, closed at both ends: it is chords that are measured across it. -/
def interval (σ : BitString) : Set ℝ := Set.Icc (G.left σ) (G.right σ)

theorem width_eq_scale_mul_dyadicWidth (σ : BitString) :
    G.width σ = G.scale * dyadicWidth σ := rfl

theorem width_pos (σ : BitString) : 0 < G.width σ :=
  mul_pos G.zero_lt_scale (dyadicWidth_pos σ)

theorem left_lt_right (σ : BitString) : G.left σ < G.right σ := by
  rw [right]
  linarith [G.width_pos σ]

@[simp] theorem left_nil : G.left [] = G.shift := by rw [left, dyadicLeft_nil]; ring

@[simp] theorem width_nil : G.width [] = G.scale := by rw [width, dyadicWidth_nil]; ring

/-! ### The child relations -/

theorem width_append (σ : BitString) (b : Bool) : G.width (σ ++ [b]) = G.width σ / 2 := by
  rw [width, width, dyadicWidth_append]
  ring

theorem left_append (σ : BitString) (b : Bool) :
    G.left (σ ++ [b]) = G.left σ + (if b then G.width σ / 2 else 0) := by
  rw [left, left, dyadicLeft_append, width]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

theorem left_append_false (σ : BitString) : G.left (σ ++ [false]) = G.left σ := by
  rw [left_append]; simp

theorem left_append_true (σ : BitString) : G.left (σ ++ [true]) = G.left σ + G.width σ / 2 := by
  rw [left_append]; simp

theorem right_append_true (σ : BitString) : G.right (σ ++ [true]) = G.right σ := by
  rw [right, right, left_append_true, width_append]
  ring

theorem right_append_false_eq_left_append_true (σ : BitString) :
    G.right (σ ++ [false]) = G.left (σ ++ [true]) := by
  rw [right, left_append_false, left_append_true, width_append]

/-! ## The coded endpoints

The fold state is `(left, width)`, both signed codes; the initial state is `(shift, scale)`. -/

/-- One step of the endpoint fold. -/
def endpointStep (p : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  if b then (RatCode.add p.1 (RatCode.half p.2), RatCode.half p.2)
  else (p.1, RatCode.half p.2)

/-- The coded left endpoint and width of the interval named by `σ`. -/
def endpointCodePair (σ : BitString) : ℕ × ℕ :=
  σ.foldl endpointStep (G.shiftCode, RatCode.ofNNRat G.scaleCode)

/-- The coded left endpoint. -/
def leftCode (σ : BitString) : ℕ := (G.endpointCodePair σ).1

/-- The coded width. -/
def widthCode (σ : BitString) : ℕ := (G.endpointCodePair σ).2

/-- The coded right endpoint. -/
def rightCode (σ : BitString) : ℕ :=
  RatCode.add (G.endpointCodePair σ).1 (G.endpointCodePair σ).2

theorem endpointCodePair_append (σ : BitString) (b : Bool) :
    G.endpointCodePair (σ ++ [b]) = endpointStep (G.endpointCodePair σ) b := by
  rw [endpointCodePair, endpointCodePair, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **The bridge.** Both components of the fold denote what they are named for. -/
theorem value_endpointCodePair (σ : BitString) :
    ((RatCode.value (G.endpointCodePair σ).1 : ℚ) : ℝ) = G.left σ ∧
      ((RatCode.value (G.endpointCodePair σ).2 : ℚ) : ℝ) = G.width σ := by
  induction σ using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_⟩
    · rw [endpointCodePair, List.foldl_nil, left_nil, shift]
    · rw [endpointCodePair, List.foldl_nil, width_nil, scale, RatCode.value_ofNNRat]
  | append_singleton σ b ih =>
    obtain ⟨ihl, ihw⟩ := ih
    have hw : ((RatCode.value (G.endpointCodePair (σ ++ [b])).2 : ℚ) : ℝ)
        = G.width (σ ++ [b]) := by
      rw [endpointCodePair_append, endpointStep, width_append, ← ihw]
      cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;>
        rw [RatCode.value_half] <;> push_cast <;> ring
    refine ⟨?_, hw⟩
    rw [endpointCodePair_append, endpointStep, left_append, ← ihl, ← ihw]
    cases b
    · simp
    · simp only [if_true]
      rw [RatCode.value_add, RatCode.value_half]
      push_cast
      ring

theorem value_leftCode (σ : BitString) :
    ((RatCode.value (G.leftCode σ) : ℚ) : ℝ) = G.left σ := (G.value_endpointCodePair σ).1

theorem value_widthCode (σ : BitString) :
    ((RatCode.value (G.widthCode σ) : ℚ) : ℝ) = G.width σ := (G.value_endpointCodePair σ).2

theorem value_rightCode (σ : BitString) :
    ((RatCode.value (G.rightCode σ) : ℚ) : ℝ) = G.right σ := by
  rw [rightCode, RatCode.value_add, Rat.cast_add, (G.value_endpointCodePair σ).1,
    (G.value_endpointCodePair σ).2, right]

/-! ### Computability -/

theorem primrec_endpointStep : Primrec₂ endpointStep := by
  have hhalf : Primrec fun p : (ℕ × ℕ) × Bool ↦ RatCode.half p.1.2 :=
    RatCode.primrec_half.comp (Primrec.snd.comp Primrec.fst)
  have htrue : Primrec fun p : (ℕ × ℕ) × Bool ↦
      (RatCode.add p.1.1 (RatCode.half p.1.2), RatCode.half p.1.2) :=
    Primrec.pair (RatCode.primrec_add.comp (Primrec.fst.comp Primrec.fst) hhalf) hhalf
  have hfalse : Primrec fun p : (ℕ × ℕ) × Bool ↦ (p.1.1, RatCode.half p.1.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) hhalf
  have hcond := Primrec.cond Primrec.snd htrue hfalse
  exact hcond.of_eq fun p ↦ by rw [endpointStep, Bool.cond_eq_ite]

theorem primrec_endpointCodePair : Primrec G.endpointCodePair := by
  have hstep : Primrec₂ fun (_ : BitString) (p : (ℕ × ℕ) × Bool) ↦ endpointStep p.1 p.2 :=
    primrec_endpointStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldl Primrec.id (Primrec.const _) hstep).of_eq fun _ ↦ rfl

theorem primrec_leftCode : Primrec G.leftCode :=
  Primrec.fst.comp G.primrec_endpointCodePair

theorem primrec_widthCode : Primrec G.widthCode :=
  Primrec.snd.comp G.primrec_endpointCodePair

theorem primrec_rightCode : Primrec G.rightCode :=
  RatCode.primrec_add.comp (Primrec.fst.comp G.primrec_endpointCodePair)
    (Primrec.snd.comp G.primrec_endpointCodePair)

/-! ## Slopes across the grid

These are the two algebraic facts the slope martingale rests on. The martingale is built later. -/

/-- **The fairness identity.** A chord's slope is the average of its two children's. -/
theorem slope_children_add (f : ℝ → ℝ) (σ : BitString) :
    slope f (G.left (σ ++ [false])) (G.right (σ ++ [false]))
        + slope f (G.left (σ ++ [true])) (G.right (σ ++ [true]))
      = 2 * slope f (G.left σ) (G.right σ) := by
  have hw : G.width σ ≠ 0 := ne_of_gt (G.width_pos σ)
  rw [right_append_true, left_append_true, right_append_false_eq_left_append_true,
    left_append_false, left_append_true, right, slope_def_field, slope_def_field,
    slope_def_field]
  have h1 : G.left σ + G.width σ / 2 - G.left σ = G.width σ / 2 := by ring
  have h2 : G.left σ + G.width σ - (G.left σ + G.width σ / 2) = G.width σ / 2 := by ring
  have h3 : G.left σ + G.width σ - G.left σ = G.width σ := by ring
  rw [h1, h2, h3]
  field_simp
  ring

theorem slope_nonneg_of_monotone {f : ℝ → ℝ} (hf : Monotone f) (σ : BitString) :
    0 ≤ slope f (G.left σ) (G.right σ) := by
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hf (G.left_lt_right σ).le))
    (sub_nonneg.mpr (G.left_lt_right σ).le)

end AffineDyadicGrid

/-! ## The modular core

The covering argument needs one mesh point of the grid `1 / (2 ^ n * k)` to be reachable as a
dyadic point of the grid `1 / 2 ^ n` shifted by a multiple of `1 / k`. That is a statement about
`ℤ` alone, and it is isolated here so that the geometry never carries arithmetic detail.

The shift is *signed*. Given `M`, the index `i` is the unique representative below `2 ^ n` with
`i * k ≡ M` modulo `2 ^ n`, and `v` is then forced to be `(M - i * k) / 2 ^ n`. Normalizing `v` to
a nonnegative residue would change the rational identity by an integer and force a compensating
change in `i`, whose range is already fixed.

Coprimality is stated as `Nat.Coprime`, not as parity: the covering proof chooses an odd `k` and
converts once, rather than carrying parity through every line. -/

theorem coprime_two_pow_of_odd {k : ℕ} (hk : Odd k) (n : ℕ) : Nat.Coprime k (2 ^ n) :=
  Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hk)

/-- **The Bézout step.** Every multiple of `1 / (2 ^ n * k)` up to `1` is a dyadic point of level
`n` shifted by an integer multiple of `1 / k`, with the multiple bounded by `k`. -/
theorem exists_dyadic_shift_decomposition {k n M : ℕ} (hk : 0 < k)
    (hcop : Nat.Coprime k (2 ^ n)) (hM : M ≤ 2 ^ n * k) :
    ∃ i : ℕ, i < 2 ^ n ∧ ∃ v : ℤ, |v| ≤ (k : ℤ) ∧ (i : ℤ) * k + v * 2 ^ n = M := by
  have hpow : (0 : ℤ) < 2 ^ n := by positivity
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  rw [Nat.cast_pow, Nat.cast_ofNat] at hab
  set q : ℤ := (M * a) / 2 ^ n with hq
  set i : ℤ := (M * a) % 2 ^ n with hi
  have hsplit : 2 ^ n * q + i = (M : ℤ) * a := Int.mul_ediv_add_emod _ _
  have hi0 : 0 ≤ i := Int.emod_nonneg _ (ne_of_gt hpow)
  have hilt : i < 2 ^ n := Int.emod_lt_of_pos _ hpow
  have hcast : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi0
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  have hMle : (M : ℤ) ≤ 2 ^ n * k := by exact_mod_cast hM
  refine ⟨i.toNat, ?_, (M : ℤ) * b + q * k, ?_, ?_⟩
  · exact_mod_cast hcast ▸ hilt
  · have hkey : ((M : ℤ) * b + q * k) * 2 ^ n = (M : ℤ) - i * k := by
      linear_combination (k : ℤ) * hsplit + (M : ℤ) * hab
    rw [abs_le]
    constructor
    · have h1 : -((k : ℤ) * 2 ^ n) ≤ ((M : ℤ) * b + q * k) * 2 ^ n := by
        rw [hkey]
        nlinarith [mul_le_mul_of_nonneg_right hilt.le hkpos.le]
      have h2 : (-(k : ℤ)) * 2 ^ n ≤ ((M : ℤ) * b + q * k) * 2 ^ n := by linarith [h1]
      exact le_of_mul_le_mul_right h2 hpow
    · have h1 : ((M : ℤ) * b + q * k) * 2 ^ n ≤ (k : ℤ) * 2 ^ n := by
        rw [hkey]
        nlinarith [mul_nonneg hi0 hkpos.le]
      exact le_of_mul_le_mul_right h1 hpow
  · rw [hcast]
    linear_combination (k : ℤ) * hsplit + (M : ℤ) * hab

/-- The rational form: the decomposition is exactly the mesh point. -/
theorem dyadic_add_shift_eq_mesh {k n M i : ℕ} {v : ℤ} (hk : 0 < k)
    (h : (i : ℤ) * k + v * 2 ^ n = M) :
    ((i : ℚ) / 2 ^ n) + (v : ℚ) / k = (M : ℚ) / (2 ^ n * k) := by
  have hk' : (k : ℚ) ≠ 0 := by positivity
  have hpow : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  have h' : (i : ℚ) * k + (v : ℚ) * 2 ^ n = (M : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) h
  field_simp
  linear_combination h'

/-! ## The finite family

For one fixed `k`, the family is indexed by `l` with `k / 2 < l ≤ k` and by the signed shift
multiplier `v` with `|v| ≤ k`. The resolution `n` and the word index `i` are *not* parameters of
the family: they are chosen per interval, and the grid is what stays fixed. Indexing by `n` as well
would make the family infinite.

A grid of the family has scale `l / k` and shift `l * v / k ^ 2`. The second is the affine
translation, not the auxiliary mesh shift `v / k`: the mesh shift is measured before rescaling, so
the translation is `p` times it.

Everything here is private. The geometry consumes only the identities below and the membership
lemma, never the shape of the family. -/

/-- The coded shift `l * v / k ^ 2`, with the sign carried by the two parts of the signed code. -/
private def shiftCodeOfLKv (k l : ℕ) (v : ℤ) : ℕ :=
  if 0 ≤ v then Nat.pair (Nat.pair (l * v.toNat) (k * k - 1)) (Nat.pair 0 0)
  else Nat.pair (Nat.pair 0 0) (Nat.pair (l * (-v).toNat) (k * k - 1))

/-- The grid with scale `l / k` and shift `l * v / k ^ 2`. -/
private def gridOfLKv (k l : ℕ) (v : ℤ) (hl : 0 < l) : AffineDyadicGrid where
  scaleCode := Nat.pair l (k - 1)
  shiftCode := shiftCodeOfLKv k l v
  scale_pos := by
    rw [NNRatCode.value_pos_iff, Nat.unpair_pair]
    exact hl

private theorem scale_gridOfLKv {k l : ℕ} {v : ℤ} (hk : 0 < k) (hl : 0 < l) :
    (gridOfLKv k l v hl).scale = (l : ℝ) / k := by
  rw [AffineDyadicGrid.scale, gridOfLKv, NNRatCode.value_pair, Nat.sub_add_cancel hk]
  push_cast
  ring

private theorem shift_gridOfLKv {k l : ℕ} {v : ℤ} (hk : 0 < k) (hl : 0 < l) :
    (gridOfLKv k l v hl).shift = (l : ℝ) * v / (k : ℝ) ^ 2 := by
  have hkk : 0 < k * k := Nat.mul_pos hk hk
  rw [AffineDyadicGrid.shift, gridOfLKv, shiftCodeOfLKv]
  by_cases hv : 0 ≤ v
  · rw [if_pos hv, RatCode.value_pair, NNRatCode.value_pair, NNRatCode.value_pair,
      Nat.sub_add_cancel hkk]
    have hto : ((v.toNat : ℕ) : ℝ) = (v : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hv
    push_cast
    rw [hto]
    ring
  · rw [if_neg hv, RatCode.value_pair, NNRatCode.value_pair, NNRatCode.value_pair,
      Nat.sub_add_cancel hkk]
    have hto : (((-v).toNat : ℕ) : ℝ) = -(v : ℝ) := by
      have h0 : (0 : ℤ) ≤ -v := by omega
      exact_mod_cast Int.toNat_of_nonneg h0
    push_cast
    rw [hto]
    ring

/-- The finite family for a fixed `k`. -/
private noncomputable def gridFamily (k : ℕ) : Finset AffineDyadicGrid :=
  letI := Classical.decEq AffineDyadicGrid
  (((Finset.Icc (k / 2 + 1) k) ×ˢ (Finset.Icc (-(k : ℤ)) (k : ℤ))).attach).image
    fun p ↦ gridOfLKv k p.1.1 p.1.2 (by
      have h := (Finset.mem_Icc.mp (Finset.mem_product.mp p.2).1).1
      omega)

/-- Membership, stated against the parameter bounds. This is the only door into the family. -/
private theorem gridOfLKv_mem_family {k l : ℕ} {v : ℤ} (hl : 0 < l) (hl1 : k / 2 < l)
    (hl2 : l ≤ k) (hv : |v| ≤ (k : ℤ)) : gridOfLKv k l v hl ∈ gridFamily k := by
  classical
  rw [gridFamily]
  refine Finset.mem_image.mpr ⟨⟨(l, v), ?_⟩, Finset.mem_attach _ _, rfl⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hl2⟩, Finset.mem_Icc.mpr ?_⟩
  exact ⟨(abs_le.mp hv).1, (abs_le.mp hv).2⟩

/-! ### The endpoint identities

With `σ` the word of length `n` at index `i`, and `i * k + v * 2 ^ n = M` the decomposition, the
left endpoint is exactly the mesh point `p * M / (2 ^ n * k)`. The width and right endpoint are
recorded here too, since the containment and distortion estimates consume all three and should not
have to reopen the bridge between codes and semantics. -/

private theorem width_gridOfLKv {k l n i : ℕ} {v : ℤ} (hk : 0 < k) (hl : 0 < l) (hi : i < 2 ^ n) :
    (gridOfLKv k l v hl).width ((BitString.wordsOfLength n).getD i [])
      = ((l : ℝ) / k) / 2 ^ n := by
  have hlt : i < (BitString.wordsOfLength n).length := by
    rw [BitString.length_wordsOfLength]; exact hi
  have hlen : ((BitString.wordsOfLength n).getD i []).length = n := by
    refine BitString.length_of_mem_wordsOfLength ?_
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem _
  rw [AffineDyadicGrid.width, scale_gridOfLKv hk hl, dyadicWidth, hlen, inv_pow, div_eq_mul_inv]
  ring

private theorem left_gridOfLKv {k l n i M : ℕ} {v : ℤ} (hk : 0 < k) (hl : 0 < l) (hi : i < 2 ^ n)
    (h : (i : ℤ) * k + v * 2 ^ n = M) :
    (gridOfLKv k l v hl).left ((BitString.wordsOfLength n).getD i [])
      = ((l : ℝ) / k) * ((M : ℝ) / (2 ^ n * k)) := by
  have hlt : i < (BitString.wordsOfLength n).length := by
    rw [BitString.length_wordsOfLength]; exact hi
  have hlen : ((BitString.wordsOfLength n).getD i []).length = n := by
    refine BitString.length_of_mem_wordsOfLength ?_
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem _
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hmesh : ((i : ℝ) / 2 ^ n) + (v : ℝ) / k = (M : ℝ) / (2 ^ n * k) := by
    have hq := congrArg (fun r : ℚ ↦ (r : ℝ)) (dyadic_add_shift_eq_mesh (i := i) hk h)
    push_cast at hq
    exact hq
  rw [AffineDyadicGrid.left, scale_gridOfLKv hk hl, shift_gridOfLKv hk hl, dyadicLeft_eq_gridPoint,
    hlen, gridIndex_getD_wordsOfLength hi, gridPoint, ← hmesh]
  field_simp

private theorem right_gridOfLKv {k l n i M : ℕ} {v : ℤ} (hk : 0 < k) (hl : 0 < l) (hi : i < 2 ^ n)
    (h : (i : ℤ) * k + v * 2 ^ n = M) :
    (gridOfLKv k l v hl).right ((BitString.wordsOfLength n).getD i [])
      = ((l : ℝ) / k) * (((M + k : ℕ) : ℝ) / (2 ^ n * k)) := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [AffineDyadicGrid.right, left_gridOfLKv hk hl hi h, width_gridOfLKv hk hl hi]
  push_cast
  field_simp

/-! ## Scale selection

The arithmetic behind the covering lemma, isolated from all geometry and stated without `α`, so
that the same lemma serves the outer construction and the inner one at `(α + 1) / 2`.

The level `n` is chosen so that `t` sits in `[(1 - 1/k) 2⁻⁽ⁿ⁺¹⁾, (1 - 1/k) 2⁻ⁿ)`, and then `l` is
the least admissible multiplier with `t + η < (l/k) 2⁻ⁿ`, where `η = 2⁻ⁿ/k` is the mesh. The first
inequality is *strict* and has to be: a cell of width exactly `t` positioned with its left endpoint
just below the target would have its right endpoint fall short. The extra mesh unit is what absorbs
the positional error, and the strictness is also what makes the inner ratio strict later.

The hypothesis is `t < 1/2`, the normalized case. Reducing a general interval to it is a separate
affine normalization, not part of this lemma. -/

private theorem exists_outer_scale {k : ℕ} (hk : 3 ≤ k) {t : ℝ} (ht : 0 < t)
    (ht_half : t < 1 / 2) :
    ∃ n l : ℕ, k / 2 < l ∧ l ≤ k ∧
      t + 1 / ((k : ℝ) * 2 ^ n) < (l : ℝ) / ((k : ℝ) * 2 ^ n) ∧
      (l : ℝ) / ((k : ℝ) * 2 ^ n) ≤ t + 2 / ((k : ℝ) * 2 ^ n) ∧
      (2⁻¹ : ℝ) ^ n ≤ 4 * t := by
  classical
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  -- The level: the last one whose scaled width still exceeds `t * k`.
  have hex : ∃ m : ℕ, ¬ (t * k < ((k : ℝ) - 1) * (2⁻¹ : ℝ) ^ m) := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < t * k / ((k : ℝ) - 1) from div_pos (by positivity) (by linarith))
      (show (2⁻¹ : ℝ) < 1 by norm_num)
    refine ⟨m, ?_⟩
    rw [not_lt]
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < (k : ℝ) - 1)] at hm
    linarith
  have hP0 : t * k < ((k : ℝ) - 1) * (2⁻¹ : ℝ) ^ 0 := by
    rw [pow_zero, mul_one]
    nlinarith
  have hfind0 : Nat.find hex ≠ 0 := by
    intro h
    have hspec := Nat.find_spec hex
    rw [h] at hspec
    exact hspec hP0
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hPn : t * k < ((k : ℝ) - 1) * (2⁻¹ : ℝ) ^ n :=
    not_not.mp (Nat.find_min hex (by omega))
  have hQn : ((k : ℝ) - 1) * (2⁻¹ : ℝ) ^ (n + 1) ≤ t * k := by
    have hspec := Nat.find_spec hex
    rw [hn, not_lt] at hspec
    exact hspec
  -- Scaled quantities.
  have hApos : (0 : ℝ) < (2⁻¹ : ℝ) ^ n := by positivity
  have hpow0 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hA : (2⁻¹ : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  have hden : (0 : ℝ) < (k : ℝ) * 2 ^ n := by positivity
  set T : ℝ := t * (k : ℝ) * 2 ^ n with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hTlt : T < (k : ℝ) - 1 := by
    have h := mul_lt_mul_of_pos_right hPn hpow0
    rw [mul_assoc ((k : ℝ) - 1), hA, mul_one] at h
    exact h
  have hTge : ((k : ℝ) - 1) / 2 ≤ T := by
    have h := mul_le_mul_of_nonneg_right hQn hpow0.le
    rw [pow_succ, mul_assoc ((k : ℝ) - 1), mul_assoc ((2⁻¹ : ℝ) ^ n), mul_comm (2⁻¹ : ℝ),
      ← mul_assoc ((2⁻¹ : ℝ) ^ n), hA, one_mul] at h
    linarith
  -- The multiplier.
  refine ⟨n, ⌊T⌋₊ + 2, ?_, ?_, ?_, ?_, ?_⟩
  · have hlt : ((k : ℝ)) / 2 < ((⌊T⌋₊ + 2 : ℕ) : ℝ) := by
      have h1 := Nat.lt_floor_add_one T
      push_cast
      linarith
    have h2 : (((k / 2 : ℕ)) : ℝ) ≤ (k : ℝ) / 2 := by
      exact_mod_cast Nat.cast_div_le
    exact_mod_cast lt_of_le_of_lt h2 hlt
  · have hfl : ⌊T⌋₊ < k - 1 := by
      rw [Nat.floor_lt hT0, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      exact hTlt
    omega
  · rw [lt_div_iff₀ hden]
    have h1 := Nat.lt_floor_add_one T
    push_cast
    field_simp
    nlinarith [h1, hden]
  · rw [div_le_iff₀ hden]
    have h2 := Nat.floor_le hT0
    push_cast
    field_simp
    nlinarith [h2, hden]
  · nlinarith [hQn, hApos, hkR, ht]

/-- The `α`-threaded form. Keeping `α` out of the selection itself is what lets the same lemma
serve the outer construction and the inner one at `(α + 1) / 2`; only the ratio bound changes, and
`8 / k` rather than `2 / k` is the true cost, since the mesh unit absorbing the positional error is
paid twice and the level is only within a factor of four of `t`. -/
private theorem exists_outer_scale_ratio {k : ℕ} (hk : 3 ≤ k) {α t : ℝ}
    (hα : 1 + 8 / (k : ℝ) < α) (ht : 0 < t) (ht_half : t < 1 / 2) :
    ∃ n l : ℕ, k / 2 < l ∧ l ≤ k ∧
      t + 1 / ((k : ℝ) * 2 ^ n) < (l : ℝ) / ((k : ℝ) * 2 ^ n) ∧
      (l : ℝ) / ((k : ℝ) * 2 ^ n) < α * t := by
  obtain ⟨n, l, hl1, hl2, hlow, hhigh, hsmall⟩ := exists_outer_scale hk ht ht_half
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  refine ⟨n, l, hl1, hl2, hlow, ?_⟩
  have heq : 2 / ((k : ℝ) * 2 ^ n) = (2 / (k : ℝ)) * (2⁻¹ : ℝ) ^ n := by
    rw [inv_pow]
    field_simp
  have hstep : 2 / ((k : ℝ) * 2 ^ n) ≤ 8 * t / (k : ℝ) := by
    rw [heq]
    calc (2 / (k : ℝ)) * (2⁻¹ : ℝ) ^ n
        ≤ (2 / (k : ℝ)) * (4 * t) := by
          exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 8 * t / (k : ℝ) := by field_simp; ring
  have hfinal : t + 8 * t / (k : ℝ) = (1 + 8 / (k : ℝ)) * t := by
    field_simp
  calc (l : ℝ) / ((k : ℝ) * 2 ^ n)
      ≤ t + 2 / ((k : ℝ) * 2 ^ n) := hhigh
    _ ≤ t + 8 * t / (k : ℝ) := by linarith
    _ = (1 + 8 / (k : ℝ)) * t := hfinal
    _ < α * t := mul_lt_mul_of_pos_right hα ht

/-! ## Positioning

The scale is chosen; what remains is to slide a cell of that scale so that it covers the target.
The mesh is `1 / k` of a cell, so the left endpoint can be placed within one mesh unit below `x`,
and the strict inequality `t + η < w` is exactly what makes the far end clear `y`.

The same normalization that bounds the interval bounds the mesh index: `x < 1/2` and `p > 1/2`
give `x / p < 1`, hence `M < 2 ^ n * k`, which is the modular theorem's hypothesis. No separate
coarse estimate is needed. -/

private theorem natCeil_sub_one_bracket {r : ℝ} (hr : 0 < r) :
    (((⌈r⌉₊ - 1 : ℕ) : ℝ) < r ∧ r ≤ (⌈r⌉₊ : ℝ)) := by
  have h1 : 1 ≤ ⌈r⌉₊ := Nat.one_le_ceil_iff.mpr hr
  refine ⟨?_, Nat.le_ceil r⟩
  rw [Nat.cast_sub h1, Nat.cast_one]
  have := Nat.ceil_lt_add_one hr.le
  linarith

private theorem exists_odd_k {α : ℝ} (hα : 1 < α) :
    ∃ k : ℕ, 3 ≤ k ∧ Odd k ∧ 1 + 8 / (k : ℝ) < α := by
  have hα0 : (0 : ℝ) < α - 1 := by linarith
  have hz : (0 : ℝ) < 8 / (α - 1) := by positivity
  have hceil : 8 / (α - 1) ≤ (⌈8 / (α - 1)⌉₊ : ℝ) := Nat.le_ceil _
  have h1 : 1 ≤ ⌈8 / (α - 1)⌉₊ := Nat.one_le_ceil_iff.mpr hz
  refine ⟨2 * ⌈8 / (α - 1)⌉₊ + 1, by omega, Nat.odd_iff.mpr (by omega), ?_⟩
  have hK0 : (0 : ℝ) < ((2 * ⌈8 / (α - 1)⌉₊ + 1 : ℕ) : ℝ) := by positivity
  have hKgt : 8 / (α - 1) < ((2 * ⌈8 / (α - 1)⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [div_lt_iff₀ hα0] at hKgt
  have h8 : (8 : ℝ) / ((2 * ⌈8 / (α - 1)⌉₊ + 1 : ℕ) : ℝ) < α - 1 := by
    rw [div_lt_iff₀ hK0]
    linarith
  linarith

private theorem exists_outer_interval_normalized {k : ℕ} (hk : 3 ≤ k) (hkodd : Odd k)
    {α x y : ℝ} (hα : 1 + 8 / (k : ℝ) < α) (hx : 0 < x) (hxy : x < y) (hy : y < 1 / 2) :
    ∃ G ∈ gridFamily k, ∃ σ, Set.Icc x y ⊆ G.interval σ ∧ G.width σ < α * (y - x) := by
  have hknat : 0 < k := by omega
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have ht : 0 < y - x := by linarith
  have ht_half : y - x < 1 / 2 := by linarith
  obtain ⟨n, l, hl1, hl2, hlow, hhigh⟩ := exists_outer_scale_ratio hk hα ht ht_half
  have hk2l : k < 2 * l := by omega
  have hl0 : 0 < l := by omega
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hlk : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hl2
  have hk2lR : (k : ℝ) < 2 * (l : ℝ) := by exact_mod_cast hk2l
  have hpow0 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hden : (0 : ℝ) < (k : ℝ) * 2 ^ n := by positivity
  set W : ℝ := (l : ℝ) / ((k : ℝ) * 2 ^ n) with hW
  set η : ℝ := 1 / ((k : ℝ) * 2 ^ n) with hηdef
  have hW0 : 0 < W := by rw [hW]; positivity
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hWk : W / k ≤ η := by
    rw [hW, hηdef, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the mesh index below `x`
  set r : ℝ := x * k / W with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  obtain ⟨hb1, hb2⟩ := natCeil_sub_one_bracket hr0
  set M : ℕ := ⌈r⌉₊ - 1 with hM
  have hceil1 : 1 ≤ ⌈r⌉₊ := Nat.one_le_ceil_iff.mpr hr0
  have hMsucc : ((⌈r⌉₊ : ℕ) : ℝ) = (M : ℝ) + 1 := by
    rw [hM, Nat.cast_sub hceil1, Nat.cast_one]
    ring
  have hrW : r * (W / k) = x := by
    rw [hr]
    field_simp
  have hM1 : (M : ℝ) * (W / k) < x := by
    rw [← hrW]
    exact mul_lt_mul_of_pos_right hb1 (by positivity)
  have hM2 : x ≤ ((M : ℝ) + 1) * (W / k) := by
    rw [← hrW, ← hMsucc]
    exact mul_le_mul_of_nonneg_right hb2 (by positivity)
  -- the modular hypothesis
  have hrlt : r < (k : ℝ) * 2 ^ n := by
    rw [hr, hW, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    have hxk : x * (k : ℝ) < (l : ℝ) := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hxk hden
    linarith [hmul, mul_comm ((l : ℝ)) ((k : ℝ) * 2 ^ n)]
  have hMle : M ≤ 2 ^ n * k := by
    have hltR : (M : ℝ) < (k : ℝ) * 2 ^ n := lt_trans hb1 hrlt
    have hnat : M < k * 2 ^ n := by exact_mod_cast hltR
    rw [mul_comm k (2 ^ n)] at hnat
    omega
  obtain ⟨i, hi, v, hv, hdec⟩ :=
    exists_dyadic_shift_decomposition hknat (coprime_two_pow_of_odd hkodd n) hMle
  refine ⟨gridOfLKv k l v hl0, gridOfLKv_mem_family hl0 hl1 hl2 hv,
    (BitString.wordsOfLength n).getD i [], ?_, ?_⟩
  · have hleft := left_gridOfLKv (k := k) (l := l) (v := v) hknat hl0 hi hdec
    have hwidth := width_gridOfLKv (k := k) (l := l) (v := v) hknat hl0 hi
    have hAeq : ((l : ℝ) / k) * ((M : ℝ) / (2 ^ n * k)) = (M : ℝ) * (W / k) := by
      rw [hW]
      field_simp
    have hWeq : ((l : ℝ) / k) / 2 ^ n = W := by
      rw [hW]
      field_simp
    rw [AffineDyadicGrid.interval, AffineDyadicGrid.right, hleft, hwidth, hAeq, hWeq]
    refine Set.Icc_subset_Icc (le_of_lt hM1) ?_
    nlinarith [hM2, hWk, hlow]
  · have hwidth := width_gridOfLKv (k := k) (l := l) (v := v) hknat hl0 hi
    have hWeq : ((l : ℝ) / k) / 2 ^ n = W := by
      rw [hW]
      field_simp
    rw [hwidth, hWeq]
    exact hhigh

end AlgorithmicRandomness
