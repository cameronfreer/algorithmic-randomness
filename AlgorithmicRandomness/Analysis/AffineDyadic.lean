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

/-! ## Cells of the whole affine grid

The grid's cells are indexed by an integer block together with a dyadic word inside it, so that
every translate of the unit cell is named — the earlier `BitString` indexing covers only the block
`0` interval, which is not enough once regridding may move to a neighbouring block.

At word length `n` the cell carries integer index `block * 2 ^ n + gridIndex word`, so each cell of
the grid occurs exactly once. Appending a bit is still the child operation, so the endpoint fold and
its correctness carry over unchanged, and no signed division enters the tree recursion. -/

/-- A cell of the affine grid: an integer block and a dyadic word within it. -/
structure AffineDyadicCell where
  /-- Which translate of the unit cell. -/
  block : ℤ
  /-- The dyadic address inside that translate. -/
  word : BitString

namespace AffineDyadicCell

/-- The child obtained by appending a bit. -/
def child (c : AffineDyadicCell) (b : Bool) : AffineDyadicCell := ⟨c.block, c.word ++ [b]⟩

@[simp] theorem child_block (c : AffineDyadicCell) (b : Bool) : (c.child b).block = c.block := rfl

@[simp] theorem child_word (c : AffineDyadicCell) (b : Bool) :
    (c.child b).word = c.word ++ [b] := rfl

/-- Whether the cell has a parent: only the block root does not. -/
def hasParent (c : AffineDyadicCell) : Bool :=
  match c.word with
  | [] => false
  | _ :: _ => true

/-- The parent cell. Total: at a block root the value is arbitrary, and `hasParent` guards every
use. It is `dropLast` on the word, written through operations the pinned mathlib knows to be
primitive recursive. -/
def parent (c : AffineDyadicCell) : AffineDyadicCell := ⟨c.block, c.word.reverse.tail.reverse⟩

@[simp] theorem hasParent_iff (c : AffineDyadicCell) : c.hasParent = true ↔ c.word ≠ [] := by
  cases hw : c.word <;> simp [hasParent, hw]

@[simp] theorem parent_child (c : AffineDyadicCell) (b : Bool) : (c.child b).parent = c := by
  rw [parent, child]
  simp

theorem exists_child_parent (c : AffineDyadicCell) (h : c.hasParent = true) :
    ∃ b : Bool, c.parent.child b = c := by
  rcases List.eq_nil_or_concat' c.word with hnil | ⟨σ, b, hσ⟩
  · exact absurd hnil ((hasParent_iff c).mp h)
  · refine ⟨b, ?_⟩
    have hpar : c.parent = ⟨c.block, σ⟩ := by
      rw [parent, hσ]
      simp
    rw [hpar, child, ← hσ]

/-- The encoding equivalence, named so that the projections can be proved once and the transported
encoding never unfolded again. -/
def equivProd : AffineDyadicCell ≃ ℤ × BitString where
  toFun c := (c.block, c.word)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

end AffineDyadicCell

instance : Primcodable AffineDyadicCell := Primcodable.ofEquiv _ AffineDyadicCell.equivProd

theorem primrec_affineDyadicCell_block : Primrec AffineDyadicCell.block :=
  Primrec.fst.comp (Primrec.of_equiv (e := AffineDyadicCell.equivProd))

theorem primrec_affineDyadicCell_word : Primrec AffineDyadicCell.word :=
  Primrec.snd.comp (Primrec.of_equiv (e := AffineDyadicCell.equivProd))

theorem primrec_affineDyadicCell_hasParent : Primrec AffineDyadicCell.hasParent := by
  have h : Primrec fun c : AffineDyadicCell ↦ decide (0 < c.word.length) :=
    primrecPred_iff_primrec_decide.mp
      (Primrec.nat_lt.comp (Primrec.const 0)
        (Primrec.list_length.comp primrec_affineDyadicCell_word))
  refine h.of_eq fun c ↦ ?_
  cases hw : c.word <;> simp [AffineDyadicCell.hasParent, hw]

theorem primrec_affineDyadicCell_parent : Primrec AffineDyadicCell.parent := by
  have hword : Primrec fun c : AffineDyadicCell ↦ c.word.reverse.tail.reverse :=
    Primrec.list_reverse.comp
      (Primrec.list_tail.comp (Primrec.list_reverse.comp primrec_affineDyadicCell_word))
  have hpair := Primrec.pair primrec_affineDyadicCell_block hword
  exact (Primrec.of_equiv_symm.comp hpair).of_eq fun _ ↦ rfl

theorem primrec_affineDyadicCell_child : Primrec₂ AffineDyadicCell.child := by
  have hblock : Primrec fun p : AffineDyadicCell × Bool ↦ p.1.block :=
    primrec_affineDyadicCell_block.comp Primrec.fst
  have hword : Primrec fun p : AffineDyadicCell × Bool ↦ p.1.word ++ [p.2] :=
    Primrec.list_append.comp (primrec_affineDyadicCell_word.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  have hpair := Primrec.pair hblock hword
  exact (Primrec.of_equiv_symm.comp hpair).of_eq fun _ ↦ rfl

namespace AffineDyadicGrid

variable (G : AffineDyadicGrid)

/-- The left endpoint of a cell. -/
noncomputable def cellLeft (c : AffineDyadicCell) : ℝ :=
  G.scale * ((c.block : ℝ) + dyadicLeft c.word) + G.shift

/-- Its width. -/
noncomputable def cellWidth (c : AffineDyadicCell) : ℝ := G.scale * dyadicWidth c.word

/-- Its right endpoint. -/
noncomputable def cellRight (c : AffineDyadicCell) : ℝ := G.cellLeft c + G.cellWidth c

/-- The closed interval it names. -/
def cellInterval (c : AffineDyadicCell) : Set ℝ := Set.Icc (G.cellLeft c) (G.cellRight c)

theorem cellWidth_pos (c : AffineDyadicCell) : 0 < G.cellWidth c :=
  mul_pos G.zero_lt_scale (dyadicWidth_pos c.word)

theorem cellLeft_lt_cellRight (c : AffineDyadicCell) : G.cellLeft c < G.cellRight c := by
  rw [cellRight]
  linarith [G.cellWidth_pos c]

/-! ### The block-zero embedding

The word-indexed cells are the block-`0` ones, so every earlier statement transfers. -/

@[simp] theorem cellLeft_mk_zero (σ : BitString) : G.cellLeft ⟨0, σ⟩ = G.left σ := by
  rw [cellLeft, AffineDyadicGrid.left]
  norm_num

@[simp] theorem cellWidth_mk_zero (σ : BitString) : G.cellWidth ⟨0, σ⟩ = G.width σ := rfl

@[simp] theorem cellRight_mk_zero (σ : BitString) : G.cellRight ⟨0, σ⟩ = G.right σ := by
  rw [cellRight, cellLeft_mk_zero, cellWidth_mk_zero, AffineDyadicGrid.right]

@[simp] theorem cellInterval_mk_zero (σ : BitString) : G.cellInterval ⟨0, σ⟩ = G.interval σ := by
  rw [cellInterval, cellLeft_mk_zero, cellRight_mk_zero, AffineDyadicGrid.interval]

/-! ### The child relations -/

theorem cellWidth_child (c : AffineDyadicCell) (b : Bool) :
    G.cellWidth (c.child b) = G.cellWidth c / 2 := by
  rw [cellWidth, cellWidth, AffineDyadicCell.child_word, dyadicWidth_append]
  ring

theorem cellLeft_child (c : AffineDyadicCell) (b : Bool) :
    G.cellLeft (c.child b) = G.cellLeft c + (if b then G.cellWidth c / 2 else 0) := by
  rw [cellLeft, cellLeft, AffineDyadicCell.child_word, AffineDyadicCell.child_block,
    dyadicLeft_append, cellWidth]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

theorem cellLeft_child_false (c : AffineDyadicCell) :
    G.cellLeft (c.child false) = G.cellLeft c := by
  rw [cellLeft_child]; simp

theorem cellLeft_child_true (c : AffineDyadicCell) :
    G.cellLeft (c.child true) = G.cellLeft c + G.cellWidth c / 2 := by
  rw [cellLeft_child]; simp

theorem cellRight_child_true (c : AffineDyadicCell) :
    G.cellRight (c.child true) = G.cellRight c := by
  rw [cellRight, cellRight, cellLeft_child_true, cellWidth_child]
  ring

theorem cellRight_child_false_eq_cellLeft_child_true (c : AffineDyadicCell) :
    G.cellRight (c.child false) = G.cellLeft (c.child true) := by
  rw [cellRight, cellLeft_child_false, cellLeft_child_true, cellWidth_child]

theorem cellLeft_le_cellLeft_child (c : AffineDyadicCell) (b : Bool) :
    G.cellLeft c ≤ G.cellLeft (c.child b) := by
  rw [cellLeft_child]
  cases b
  · simp
  · simp only [if_true]
    linarith [G.cellWidth_pos c]

theorem cellRight_child_le_cellRight (c : AffineDyadicCell) (b : Bool) :
    G.cellRight (c.child b) ≤ G.cellRight c := by
  rw [cellRight, cellRight, cellLeft_child, cellWidth_child]
  cases b
  · simp only [Bool.false_eq_true, if_false, add_zero]
    linarith [G.cellWidth_pos c]
  · simp only [if_true]
    linarith

theorem cellInterval_child_subset (c : AffineDyadicCell) (b : Bool) :
    G.cellInterval (c.child b) ⊆ G.cellInterval c :=
  Set.Icc_subset_Icc (G.cellLeft_le_cellLeft_child c b) (G.cellRight_child_le_cellRight c b)

theorem cellInterval_subset_parent (c : AffineDyadicCell) (h : c.hasParent = true) :
    G.cellInterval c ⊆ G.cellInterval c.parent := by
  obtain ⟨b, hb⟩ := AffineDyadicCell.exists_child_parent c h
  have hsub := G.cellInterval_child_subset c.parent b
  rw [hb] at hsub
  exact hsub

theorem cellWidth_parent (c : AffineDyadicCell) (h : c.hasParent = true) :
    G.cellWidth c = G.cellWidth c.parent / 2 := by
  obtain ⟨b, hb⟩ := AffineDyadicCell.exists_child_parent c h
  have hw := G.cellWidth_child c.parent b
  rw [hb] at hw
  exact hw

/-- **The index identity.** A cell of word length `n` is the affine image of the interval of
integer index `block * 2 ^ n + gridIndex word` at level `n`. -/
theorem cellLeft_eq_index (c : AffineDyadicCell) :
    G.cellLeft c
      = G.scale * (((c.block * 2 ^ c.word.length + gridIndex c.word : ℤ) : ℝ)
        / 2 ^ c.word.length) + G.shift := by
  have hpow : ((2 : ℝ)) ^ c.word.length ≠ 0 := by positivity
  rw [cellLeft, dyadicLeft_eq_gridPoint, gridPoint]
  push_cast
  field_simp

end AffineDyadicGrid

/-! ## Coded rational intervals

An interval is coded by its left endpoint and its *nonnegative* width, rather than by two signed
endpoints: halving is then one nonnegative operation, the half-width test stays in `ℚ≥0`, and an
inconsistent endpoint order is impossible. Validity is an external invariant, so the executable
structure carries no proof field.

Cells are coded by the same child fold that produces them, never by a closed-form sum. Coded
rationals are not canonical, so two semantically equal formulas need not be equal as naturals, and
only the fold gives the exact code-level identity `cellCode (child c b) = child (cellCode c) b`. -/

/-- A rational interval: a signed left endpoint and a nonnegative width. -/
structure RatIntervalCode where
  /-- The left endpoint, as a signed code. -/
  leftCode : ℕ
  /-- The width, as a nonnegative code. -/
  widthCode : ℕ

namespace RatIntervalCode

/-- The right endpoint. -/
def rightCode (A : RatIntervalCode) : ℕ := RatCode.add A.leftCode (RatCode.ofNNRat A.widthCode)

/-- The interval is nondegenerate. Kept outside the structure, as an invariant of use. -/
def Valid (A : RatIntervalCode) : Prop := 0 < NNRatCode.value A.widthCode

noncomputable def left (A : RatIntervalCode) : ℝ := ((RatCode.value A.leftCode : ℚ) : ℝ)

noncomputable def width (A : RatIntervalCode) : ℝ :=
  ((NNRatCode.value A.widthCode : ℚ≥0) : ℝ)

noncomputable def right (A : RatIntervalCode) : ℝ := A.left + A.width

/-- The closed interval it names. -/
def interval (A : RatIntervalCode) : Set ℝ := Set.Icc A.left A.right

theorem value_rightCode (A : RatIntervalCode) :
    ((RatCode.value A.rightCode : ℚ) : ℝ) = A.right := by
  rw [rightCode, RatCode.value_add, RatCode.value_ofNNRat, Rat.cast_add, RatIntervalCode.right,
    RatIntervalCode.left, RatIntervalCode.width]
  push_cast
  ring

theorem width_nonneg (A : RatIntervalCode) : 0 ≤ A.width := by
  rw [width]
  positivity

theorem width_pos (A : RatIntervalCode) (h : A.Valid) : 0 < A.width := by
  rw [width]
  exact_mod_cast h

theorem left_lt_right (A : RatIntervalCode) (h : A.Valid) : A.left < A.right := by
  rw [right]
  linarith [A.width_pos h]

/-- The unit interval. -/
def unit : RatIntervalCode := ⟨RatCode.ofNat 0, NNRatCode.ofNat 1⟩

@[simp] theorem left_unit : unit.left = 0 := by
  rw [left, unit, RatCode.value_ofNat]
  norm_num

@[simp] theorem width_unit : unit.width = 1 := by
  rw [width, unit, NNRatCode.value_ofNat]
  norm_num

@[simp] theorem interval_unit : unit.interval = Set.Icc (0 : ℝ) 1 := by
  rw [interval, left_unit, right, left_unit, width_unit]
  norm_num

/-- The child obtained by halving. -/
def child (A : RatIntervalCode) (b : Bool) : RatIntervalCode :=
  { leftCode :=
      if b then RatCode.add A.leftCode (RatCode.ofNNRat (NNRatCode.half A.widthCode))
      else A.leftCode
    widthCode := NNRatCode.half A.widthCode }

@[simp] theorem width_child (A : RatIntervalCode) (b : Bool) :
    (A.child b).width = A.width / 2 := by
  rw [width, child, NNRatCode.value_half, width]
  push_cast
  ring

theorem left_child (A : RatIntervalCode) (b : Bool) :
    (A.child b).left = A.left + (if b then A.width / 2 else 0) := by
  rw [RatIntervalCode.left, RatIntervalCode.left, RatIntervalCode.width, child]
  cases b
  · simp
  · simp only [if_true]
    rw [RatCode.value_add, RatCode.value_ofNNRat, NNRatCode.value_half]
    push_cast
    ring

/-- The encoding equivalence. -/
def equivProd : RatIntervalCode ≃ ℕ × ℕ where
  toFun A := (A.leftCode, A.widthCode)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

end RatIntervalCode

instance : Primcodable RatIntervalCode := Primcodable.ofEquiv _ RatIntervalCode.equivProd

theorem primrec_ratIntervalCode_leftCode : Primrec RatIntervalCode.leftCode :=
  Primrec.fst.comp (Primrec.of_equiv (e := RatIntervalCode.equivProd))

theorem primrec_ratIntervalCode_widthCode : Primrec RatIntervalCode.widthCode :=
  Primrec.snd.comp (Primrec.of_equiv (e := RatIntervalCode.equivProd))

theorem primrec_ratIntervalCode_child : Primrec₂ RatIntervalCode.child := by
  have hleft : Primrec fun p : RatIntervalCode × Bool ↦ p.1.leftCode :=
    primrec_ratIntervalCode_leftCode.comp Primrec.fst
  have hwidth : Primrec fun p : RatIntervalCode × Bool ↦ p.1.widthCode :=
    primrec_ratIntervalCode_widthCode.comp Primrec.fst
  have hhalf : Primrec fun p : RatIntervalCode × Bool ↦ NNRatCode.half p.1.widthCode :=
    NNRatCode.primrec_half.comp hwidth
  have hadd : Primrec fun p : RatIntervalCode × Bool ↦
      RatCode.add p.1.leftCode (RatCode.ofNNRat (NNRatCode.half p.1.widthCode)) :=
    RatCode.primrec_add.comp hleft (RatCode.primrec_ofNNRat.comp hhalf)
  have hcond := Primrec.cond Primrec.snd hadd hleft
  have hpair := Primrec.pair hcond hhalf
  refine (Primrec.of_equiv_symm.comp hpair).of_eq fun p ↦ ?_
  cases p.2 <;> simp [RatIntervalCode.child, RatIntervalCode.equivProd]

namespace AffineDyadicGrid

variable (G : AffineDyadicGrid)

/-- The root cell of a block: the whole translate. -/
def cellRootCode (block : ℤ) : RatIntervalCode :=
  { leftCode := RatCode.add G.shiftCode (RatCode.ofIntMulNNRat block G.scaleCode)
    widthCode := G.scaleCode }

/-- A cell's code, produced by the same child fold that produces the cell. -/
def cellCode (c : AffineDyadicCell) : RatIntervalCode :=
  c.word.foldl RatIntervalCode.child (G.cellRootCode c.block)

/-- **The code-level seam.** -/
theorem cellCode_child (c : AffineDyadicCell) (b : Bool) :
    G.cellCode (c.child b) = (G.cellCode c).child b := by
  rw [cellCode, cellCode, AffineDyadicCell.child_word, AffineDyadicCell.child_block,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem left_cellRootCode (m : ℤ) : (G.cellRootCode m).left = G.cellLeft ⟨m, []⟩ := by
  rw [RatIntervalCode.left, cellRootCode, RatCode.value_add, RatCode.value_ofIntMulNNRat,
    cellLeft, dyadicLeft_nil, AffineDyadicGrid.scale, AffineDyadicGrid.shift]
  push_cast
  ring

theorem width_cellRootCode (m : ℤ) : (G.cellRootCode m).width = G.cellWidth ⟨m, []⟩ := by
  rw [RatIntervalCode.width, cellRootCode, cellWidth, dyadicWidth_nil, AffineDyadicGrid.scale]
  push_cast
  ring

/-- **The bridge.** The coded interval is the cell. -/
theorem value_cellCode (m : ℤ) (σ : BitString) :
    (G.cellCode ⟨m, σ⟩).left = G.cellLeft ⟨m, σ⟩ ∧
      (G.cellCode ⟨m, σ⟩).width = G.cellWidth ⟨m, σ⟩ := by
  induction σ using List.reverseRecOn with
  | nil => exact ⟨G.left_cellRootCode m, G.width_cellRootCode m⟩
  | append_singleton σ b ih =>
    have hchild : (⟨m, σ ++ [b]⟩ : AffineDyadicCell) = (⟨m, σ⟩ : AffineDyadicCell).child b := rfl
    rw [hchild, G.cellCode_child]
    refine ⟨?_, ?_⟩
    · rw [RatIntervalCode.left_child, ih.1, ih.2, cellLeft_child]
    · rw [RatIntervalCode.width_child, ih.2, cellWidth_child]

theorem left_cellCode (c : AffineDyadicCell) : (G.cellCode c).left = G.cellLeft c :=
  (G.value_cellCode c.block c.word).1

theorem width_cellCode (c : AffineDyadicCell) : (G.cellCode c).width = G.cellWidth c :=
  (G.value_cellCode c.block c.word).2

theorem right_cellCode (c : AffineDyadicCell) : (G.cellCode c).right = G.cellRight c := by
  rw [RatIntervalCode.right, left_cellCode, width_cellCode, cellRight]

theorem interval_cellCode (c : AffineDyadicCell) : (G.cellCode c).interval = G.cellInterval c := by
  rw [RatIntervalCode.interval, left_cellCode, right_cellCode, cellInterval]

theorem primrec_cellRootCode : Primrec G.cellRootCode := by
  have hleft : Primrec fun m : ℤ ↦
      RatCode.add G.shiftCode (RatCode.ofIntMulNNRat m G.scaleCode) :=
    RatCode.primrec_add.comp (Primrec.const _)
      (RatCode.primrec_ofIntMulNNRat.comp Primrec.id (Primrec.const _))
  have hpair := Primrec.pair hleft (Primrec.const G.scaleCode)
  exact (Primrec.of_equiv_symm.comp hpair).of_eq fun _ ↦ rfl

theorem primrec_cellCode : Primrec G.cellCode := by
  have hstep : Primrec₂ fun (_ : AffineDyadicCell) (p : RatIntervalCode × Bool) ↦
      RatIntervalCode.child p.1 p.2 :=
    primrec_ratIntervalCode_child.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldl primrec_affineDyadicCell_word
    (G.primrec_cellRootCode.comp primrec_affineDyadicCell_block) hstep).of_eq fun _ ↦ rfl

end AffineDyadicGrid

/-! ## Eligibility and regridding

A cell is eligible for a parent interval when it lies inside it and, if the half-width flag is set,
is at most half as wide. A regridding child is an eligible cell whose immediate parent is not
eligible; the block root has no parent. Since eligibility is inherited by descendants, checking the
immediate parent is the same as maximality, and it stays executable. -/

/-- The eligibility test. -/
def eligible (A : RatIntervalCode) (G : AffineDyadicGrid) (half : Bool) (c : AffineDyadicCell) :
    Bool :=
  RatCode.le A.leftCode (G.cellCode c).leftCode &&
    RatCode.le (G.cellCode c).rightCode A.rightCode &&
    (!half || NNRatCode.le (NNRatCode.double (G.cellCode c).widthCode) A.widthCode)

theorem eligible_iff {A : RatIntervalCode} {G : AffineDyadicGrid} {half : Bool}
    {c : AffineDyadicCell} :
    eligible A G half c = true ↔
      (A.left ≤ G.cellLeft c ∧ G.cellRight c ≤ A.right) ∧
        (half = true → 2 * G.cellWidth c ≤ A.width) := by
  have hL : (RatCode.value A.leftCode ≤ RatCode.value (G.cellCode c).leftCode)
      ↔ A.left ≤ G.cellLeft c := by
    rw [← G.left_cellCode c, RatIntervalCode.left, RatIntervalCode.left]
    exact_mod_cast Iff.rfl
  have hR : (RatCode.value (G.cellCode c).rightCode ≤ RatCode.value A.rightCode)
      ↔ G.cellRight c ≤ A.right := by
    have h1 : ((RatCode.value (G.cellCode c).rightCode : ℚ) : ℝ) = G.cellRight c := by
      rw [RatIntervalCode.value_rightCode, G.right_cellCode c]
    have h2 : ((RatCode.value A.rightCode : ℚ) : ℝ) = A.right := RatIntervalCode.value_rightCode A
    constructor
    · intro h
      rw [← h1, ← h2]
      exact_mod_cast h
    · intro h
      rw [← h1, ← h2] at h
      exact_mod_cast h
  have hW : (NNRatCode.value (NNRatCode.double (G.cellCode c).widthCode)
      ≤ NNRatCode.value A.widthCode) ↔ 2 * G.cellWidth c ≤ A.width := by
    rw [NNRatCode.value_double]
    have h1 : ((NNRatCode.value (G.cellCode c).widthCode : ℚ≥0) : ℝ) = G.cellWidth c := by
      rw [← G.width_cellCode c, RatIntervalCode.width]
    constructor
    · intro h
      rw [← h1, RatIntervalCode.width]
      exact_mod_cast h
    · intro h
      rw [← h1, RatIntervalCode.width] at h
      exact_mod_cast h
  rw [eligible, Bool.and_eq_true, Bool.and_eq_true, RatCode.le_iff, RatCode.le_iff, hL, hR]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun hhalf ↦ ?_⟩
    rw [hhalf] at h3
    simp only [Bool.not_true, Bool.false_or, NNRatCode.le_iff] at h3
    exact hW.mp h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    cases hhalf : half
    · simp
    · simp only [Bool.not_true, Bool.false_or, NNRatCode.le_iff]
      exact hW.mpr (h3 hhalf)

/-- **Eligibility is inherited by descendants**, which is what makes "immediate parent ineligible"
the same as "no proper ancestor eligible". -/
theorem eligible_child {A : RatIntervalCode} {G : AffineDyadicGrid} {half : Bool}
    {c : AffineDyadicCell} (h : eligible A G half c = true) (b : Bool) :
    eligible A G half (c.child b) = true := by
  rw [eligible_iff] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨le_trans h1 (G.cellLeft_le_cellLeft_child c b),
    le_trans (G.cellRight_child_le_cellRight c b) h2⟩, fun hhalf ↦ ?_⟩
  rw [G.cellWidth_child c b]
  have := h3 hhalf
  linarith [G.cellWidth_pos c]

/-- The regridding children of a parent interval: eligible, with an ineligible immediate parent. -/
def regridChild (A : RatIntervalCode) (G : AffineDyadicGrid) (half : Bool)
    (c : AffineDyadicCell) : Bool :=
  eligible A G half c && (!c.hasParent || !eligible A G half c.parent)

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

-- The grids carry a proof field, so equality is not decidable by structure; one classical
-- instance, local to this file, keeps every `Finset.image` below on the same footing.
@[reducible] private noncomputable def decEqAffineDyadicGrid : DecidableEq AffineDyadicGrid :=
  Classical.decEq _

attribute [local instance] decEqAffineDyadicGrid

/-- The finite family for a fixed `k`. -/
private noncomputable def gridFamily (k : ℕ) : Finset AffineDyadicGrid :=
  (((Finset.Icc (k / 2 + 1) k) ×ˢ (Finset.Icc (-(k : ℤ)) (k : ℤ))).attach).image
    fun p ↦ gridOfLKv k p.1.1 p.1.2 (by
      have h := (Finset.mem_Icc.mp (Finset.mem_product.mp p.2).1).1
      omega)

/-- Membership, stated against the parameter bounds. This is the only door into the family. -/
private theorem gridOfLKv_mem_family {k l : ℕ} {v : ℤ} (hl : 0 < l) (hl1 : k / 2 < l)
    (hl2 : l ≤ k) (hv : |v| ≤ (k : ℤ)) : gridOfLKv k l v hl ∈ gridFamily k := by
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

private theorem exists_outer_interval_normalized_strict {k : ℕ} (hk : 3 ≤ k) (hkodd : Odd k)
    {α x y : ℝ} (hα : 1 + 8 / (k : ℝ) < α) (hx : 0 < x) (hxy : x < y) (hy : y < 1 / 2) :
    ∃ G ∈ gridFamily k, ∃ σ,
      G.left σ < x ∧ y < G.right σ ∧ G.width σ < α * (y - x) := by
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
  have hleft := left_gridOfLKv (k := k) (l := l) (v := v) hknat hl0 hi hdec
  have hwidth := width_gridOfLKv (k := k) (l := l) (v := v) hknat hl0 hi
  have hAeq : ((l : ℝ) / k) * ((M : ℝ) / (2 ^ n * k)) = (M : ℝ) * (W / k) := by
    rw [hW]
    field_simp
  have hWeq : ((l : ℝ) / k) / 2 ^ n = W := by
    rw [hW]
    field_simp
  refine ⟨gridOfLKv k l v hl0, gridOfLKv_mem_family hl0 hl1 hl2 hv,
    (BitString.wordsOfLength n).getD i [], ?_, ?_, ?_⟩
  · rw [hleft, hAeq]
    exact hM1
  · rw [AffineDyadicGrid.right, hleft, hwidth, hAeq, hWeq]
    nlinarith [hM2, hWk, hlow]
  · rw [hwidth, hWeq]
    exact hhigh

/-- The subset-shaped form. The strict core is kept, because the inner approximation needs the
strict endpoint inequalities to produce a strict ratio. -/
private theorem exists_outer_interval_normalized {k : ℕ} (hk : 3 ≤ k) (hkodd : Odd k)
    {α x y : ℝ} (hα : 1 + 8 / (k : ℝ) < α) (hx : 0 < x) (hxy : x < y) (hy : y < 1 / 2) :
    ∃ G ∈ gridFamily k, ∃ σ, Set.Icc x y ⊆ G.interval σ ∧ G.width σ < α * (y - x) := by
  obtain ⟨G, hG, σ, h1, h2, h3⟩ :=
    exists_outer_interval_normalized_strict hk hkodd hα hx hxy hy
  refine ⟨G, hG, σ, ?_, h3⟩
  rw [AffineDyadicGrid.interval]
  exact Set.Icc_subset_Icc h1.le h2.le

/-! ## Doubling, and the general interval

Halving a target interval into `(0, 1/2)` and doubling the resulting grid is the whole of the
normalization. Doubling acts on both codes, so it stays inside the coded layer, and the membership
equivalence below makes the transport of containment definitional rather than a `Set.image`
argument. Every endpoint gap scales by two, so strict inequalities survive. -/

private def doubleGrid (G : AffineDyadicGrid) : AffineDyadicGrid where
  scaleCode := NNRatCode.double G.scaleCode
  shiftCode := RatCode.double G.shiftCode
  scale_pos := by
    rw [NNRatCode.value_double]
    exact mul_pos two_pos G.scale_pos

private theorem scale_doubleGrid (G : AffineDyadicGrid) :
    (doubleGrid G).scale = 2 * G.scale := by
  rw [AffineDyadicGrid.scale, AffineDyadicGrid.scale, doubleGrid, NNRatCode.value_double]
  push_cast
  ring

private theorem shift_doubleGrid (G : AffineDyadicGrid) :
    (doubleGrid G).shift = 2 * G.shift := by
  rw [AffineDyadicGrid.shift, AffineDyadicGrid.shift, doubleGrid, RatCode.value_double]
  push_cast
  ring

private theorem left_doubleGrid (G : AffineDyadicGrid) (σ : BitString) :
    (doubleGrid G).left σ = 2 * G.left σ := by
  rw [AffineDyadicGrid.left, AffineDyadicGrid.left, scale_doubleGrid, shift_doubleGrid]
  ring

private theorem width_doubleGrid (G : AffineDyadicGrid) (σ : BitString) :
    (doubleGrid G).width σ = 2 * G.width σ := by
  rw [AffineDyadicGrid.width, AffineDyadicGrid.width, scale_doubleGrid]
  ring

private theorem right_doubleGrid (G : AffineDyadicGrid) (σ : BitString) :
    (doubleGrid G).right σ = 2 * G.right σ := by
  rw [AffineDyadicGrid.right, AffineDyadicGrid.right, left_doubleGrid, width_doubleGrid]
  ring

private noncomputable def normalizedGridFamily (k : ℕ) : Finset AffineDyadicGrid :=
  (gridFamily k).image doubleGrid

private theorem mem_normalizedGridFamily {k : ℕ} {G : AffineDyadicGrid} (hG : G ∈ gridFamily k) :
    doubleGrid G ∈ normalizedGridFamily k := by
  rw [normalizedGridFamily]
  exact Finset.mem_image_of_mem _ hG

/-- **The outer approximation**, on the whole interior and still strict. -/
private theorem exists_outer_interval_strict {k : ℕ} (hk : 3 ≤ k) (hkodd : Odd k)
    {α x y : ℝ} (hα : 1 + 8 / (k : ℝ) < α) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    ∃ G ∈ normalizedGridFamily k, ∃ σ,
      G.left σ < x ∧ y < G.right σ ∧ G.width σ < α * (y - x) := by
  obtain ⟨G, hG, σ, h1, h2, h3⟩ := exists_outer_interval_normalized_strict hk hkodd hα
    (by linarith : (0 : ℝ) < x / 2) (by linarith : x / 2 < y / 2) (by linarith : y / 2 < 1 / 2)
  have h3' : G.width σ < α * (y - x) / 2 := by
    rw [show α * (y - x) / 2 = α * (y / 2 - x / 2) by ring]
    exact h3
  refine ⟨doubleGrid G, mem_normalizedGridFamily hG, σ, ?_, ?_, ?_⟩
  · rw [left_doubleGrid]
    linarith
  · rw [right_doubleGrid]
    linarith
  · rw [width_doubleGrid]
    linarith

/-! ## The inner approximation

Shrink the target by `ε h` at each end, cover the shrunken interval from outside at precision
`α₀ = 1 + ε`, and the covering interval is trapped strictly inside the original. The two shaves and
the outer slack are chosen so that they cancel exactly: with `h = (y - x) / α` the covered width is
below `(1 + ε) h`, while the room available at each end is `ε h`, and `1 + 2ε = α`.

This consumes the *strict* outer theorem. With only the subset form, `a < u` and `v < b` would
degrade to `≤` and the conclusion would be `y - x ≤ α * width`. -/

private theorem exists_inner_interval {k : ℕ} (hk : 3 ≤ k) (hkodd : Odd k) {α x y : ℝ}
    (hα : 1 < α) (hkα : 1 + 8 / (k : ℝ) < (α + 1) / 2) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    ∃ G ∈ normalizedGridFamily k, ∃ σ,
      G.interval σ ⊆ Set.Icc x y ∧ y - x < α * G.width σ := by
  have hα0 : 0 < α := by linarith
  set ε : ℝ := (α - 1) / 2 with hε
  set h : ℝ := (y - x) / α with hh
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hh0 : 0 < h := by rw [hh]; positivity
  have hyx : y - x = α * h := by rw [hh]; field_simp
  have hu0 : 0 < x + ε * h := by positivity
  have huv : x + ε * h < y - ε * h := by nlinarith
  have hv1 : y - ε * h < 1 := by nlinarith
  obtain ⟨G, hG, σ, ha, hb, hw⟩ :=
    exists_outer_interval_strict hk hkodd (α := (α + 1) / 2) hkα hu0 huv hv1
  have hdiff : (y - ε * h) - (x + ε * h) = h := by rw [hε]; ring_nf; linarith [hyx]
  have hwlt : G.width σ < (1 + ε) * h := by
    rw [hdiff] at hw
    calc G.width σ < (α + 1) / 2 * h := hw
      _ = (1 + ε) * h := by rw [hε]; ring
  have hright : G.right σ = G.left σ + G.width σ := rfl
  refine ⟨G, hG, σ, ?_, ?_⟩
  · rw [AffineDyadicGrid.interval]
    refine Set.Icc_subset_Icc ?_ ?_
    · nlinarith [hb, hwlt, hright]
    · nlinarith [ha, hwlt, hright]
  · have hlt : h < G.width σ := by
      rw [hright] at hb
      nlinarith [ha, hb, hdiff]
    nlinarith [hlt, hyx]

/-! ## The covering lemma -/

/-- **BMN Lemma 4.1.** One finite family of rationally scaled and shifted dyadic grids approximates
every interval interior to `(0, 1)` from both sides, to any rational precision.

A single family serves both conclusions: it is chosen at precision `(α + 1) / 2`, which is below
`α` for the outer approximation and is exactly what the inner construction needs.

The family is *semantic*: it is not computed uniformly from a code for `α`. That stronger
transformation, which BMN remark on, is not part of this development. It is not needed here,
because every member already carries concrete natural codes for its scale and shift, so a grid
selected later still yields an actual computable object. -/
theorem exists_finite_affineDyadicGrids {α : ℚ} (hα : 1 < α) :
    ∃ grids : Finset AffineDyadicGrid,
      (∀ {x y : ℝ}, 0 < x → x < y → y < 1 →
        ∃ G ∈ grids, ∃ σ, Set.Icc x y ⊆ G.interval σ ∧ G.width σ < (α : ℝ) * (y - x)) ∧
      (∀ {x y : ℝ}, 0 < x → x < y → y < 1 →
        ∃ G ∈ grids, ∃ σ, G.interval σ ⊆ Set.Icc x y ∧ y - x < (α : ℝ) * G.width σ) := by
  have hαR : (1 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hα0 : (1 : ℝ) < ((α : ℝ) + 1) / 2 := by linarith
  obtain ⟨k, hk, hkodd, hkα⟩ := exists_odd_k hα0
  refine ⟨normalizedGridFamily k, ?_, ?_⟩
  · intro x y hx hxy hy
    obtain ⟨G, hG, σ, hl, hr, hw⟩ := exists_outer_interval_strict hk hkodd hkα hx hxy hy
    refine ⟨G, hG, σ, ?_, ?_⟩
    · rw [AffineDyadicGrid.interval]
      exact Set.Icc_subset_Icc hl.le hr.le
    · nlinarith [hw, hxy]
  · intro x y hx hxy hy
    exact exists_inner_interval hk hkodd hαR hkα hx hxy hy

end AlgorithmicRandomness
