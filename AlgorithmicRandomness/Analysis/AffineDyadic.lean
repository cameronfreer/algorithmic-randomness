/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.Dyadic
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

end AlgorithmicRandomness
