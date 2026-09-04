/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.BinaryExpansion
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

The two slope facts are the algebra the martingale construction consumes: the children's slopes
average to the parent's, and monotone functions have nonnegative slopes. The martingale itself is
deliberately not built here.

Cells of the *whole* grid, their codes, and the coded eligibility tests follow. BMN's finite
covering family, which is the only consumer of the mesh arithmetic, lives in `AffineCovering.lean`.
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

/-! ## Refinement

Regridding children can have different depths, so the intersection argument is organized around
structural refinement — same block, one word a prefix of the other — rather than around equal word
lengths. -/

/-- `c.Refines d` when `d` is a descendant of `c`. -/
def AffineDyadicCell.Refines (c d : AffineDyadicCell) : Prop :=
  c.block = d.block ∧ c.word <+: d.word

theorem AffineDyadicCell.parent_word (c : AffineDyadicCell) : c.parent.word = c.word.dropLast := by
  rw [parent]
  induction c.word using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b _ => simp

namespace AffineDyadicGrid

variable (G : AffineDyadicGrid)

private theorem cellInterval_append_subset (m : ℤ) (σ τ : BitString) :
    G.cellInterval ⟨m, σ ++ τ⟩ ⊆ G.cellInterval ⟨m, σ⟩ := by
  induction τ using List.reverseRecOn with
  | nil => simp
  | append_singleton τ b ih =>
    have hchild : (⟨m, σ ++ (τ ++ [b])⟩ : AffineDyadicCell)
        = (⟨m, σ ++ τ⟩ : AffineDyadicCell).child b := by
      rw [AffineDyadicCell.child, ← List.append_assoc]
    rw [hchild]
    exact subset_trans (G.cellInterval_child_subset _ b) ih

theorem cellInterval_subset_of_refines {c d : AffineDyadicCell} (h : c.Refines d) :
    G.cellInterval d ⊆ G.cellInterval c := by
  obtain ⟨hb, τ, hτ⟩ := h
  have hd : d = (⟨c.block, c.word ++ τ⟩ : AffineDyadicCell) := by
    rw [hb, hτ]
  rw [hd]
  exact G.cellInterval_append_subset c.block c.word τ

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

theorem primrec_ratIntervalCode_rightCode : Primrec RatIntervalCode.rightCode :=
  RatCode.primrec_add.comp primrec_ratIntervalCode_leftCode
    (RatCode.primrec_ofNNRat.comp primrec_ratIntervalCode_widthCode)

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

private theorem eligible_append {A : RatIntervalCode} {G : AffineDyadicGrid} {half : Bool}
    {m : ℤ} {σ : BitString} (h : eligible A G half ⟨m, σ⟩ = true) (τ : BitString) :
    eligible A G half ⟨m, σ ++ τ⟩ = true := by
  induction τ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton τ b ih =>
    have hchild : (⟨m, σ ++ (τ ++ [b])⟩ : AffineDyadicCell)
        = (⟨m, σ ++ τ⟩ : AffineDyadicCell).child b := by
      rw [AffineDyadicCell.child, ← List.append_assoc]
    rw [hchild]
    exact eligible_child ih b

theorem eligible_of_refines {A : RatIntervalCode} {G : AffineDyadicGrid} {half : Bool}
    {c d : AffineDyadicCell} (hcd : c.Refines d) (h : eligible A G half c = true) :
    eligible A G half d = true := by
  obtain ⟨hb, τ, hτ⟩ := hcd
  have hd : d = (⟨c.block, c.word ++ τ⟩ : AffineDyadicCell) := by rw [hb, hτ]
  rw [hd]
  exact eligible_append (by simpa using h) τ

/-- **Refinement collapses regridding children.** Two of them related by refinement are equal:
otherwise the outer one's eligibility would propagate to the inner one's parent. -/
theorem regridChild_eq_of_refines {A : RatIntervalCode} {G : AffineDyadicGrid} {half : Bool}
    {c d : AffineDyadicCell} (hc : regridChild A G half c = true)
    (hd : regridChild A G half d = true) (hcd : c.Refines d) : c = d := by
  rw [regridChild, Bool.and_eq_true] at hc hd
  by_contra hne
  obtain ⟨hb, hpre⟩ := hcd
  have hlen : c.word.length < d.word.length := by
    rcases lt_or_eq_of_le hpre.length_le with h | h
    · exact h
    · exact absurd (by
        have hw : c.word = d.word := hpre.eq_of_length h
        cases c
        cases d
        simp_all) hne
  have hdne : d.word ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
  have hdparent : d.hasParent = true := (AffineDyadicCell.hasParent_iff d).mpr hdne
  have hdrop : c.word <+: d.word.dropLast := by
    refine List.prefix_of_prefix_length_le hpre (List.dropLast_prefix d.word) ?_
    rw [List.length_dropLast]
    omega
  have hrefpar : c.Refines d.parent := by
    refine ⟨by rw [hb, AffineDyadicCell.parent], ?_⟩
    rw [AffineDyadicCell.parent_word]
    exact hdrop
  have hel := eligible_of_refines hrefpar hc.1
  have hd2 := hd.2
  rw [hdparent, hel] at hd2
  simp at hd2

/-! ### Executability

Both tests are primitive recursive uniformly in the parent interval, since every ingredient is: the
cell code is a fold of a primitive recursive step, the interval projections are transported through
the encoding equivalence, and the two comparisons are coded rational order tests. The grid and the
half-width flag stay parameters; they are fixed data at every use. -/

theorem primrec_eligible (G : AffineDyadicGrid) (half : Bool) :
    Primrec₂ fun (A : RatIntervalCode) (c : AffineDyadicCell) ↦ eligible A G half c := by
  have hA : Primrec fun p : RatIntervalCode × AffineDyadicCell ↦ p.1 := Primrec.fst
  have hc : Primrec fun p : RatIntervalCode × AffineDyadicCell ↦ p.2 := Primrec.snd
  have hcell := G.primrec_cellCode.comp hc
  have hlow := RatCode.primrec_le.comp (primrec_ratIntervalCode_leftCode.comp hA)
    (primrec_ratIntervalCode_leftCode.comp hcell)
  have hhigh := RatCode.primrec_le.comp (primrec_ratIntervalCode_rightCode.comp hcell)
    (primrec_ratIntervalCode_rightCode.comp hA)
  have hnarrow := NNRatCode.primrec_le.comp
    (NNRatCode.primrec_double.comp (primrec_ratIntervalCode_widthCode.comp hcell))
    (primrec_ratIntervalCode_widthCode.comp hA)
  have hflag := Primrec.or.comp (Primrec.const (!half)) hnarrow
  exact ((Primrec.and.comp (Primrec.and.comp hlow hhigh) hflag)).of_eq fun _ ↦ rfl

theorem primrec_regridChild (G : AffineDyadicGrid) (half : Bool) :
    Primrec₂ fun (A : RatIntervalCode) (c : AffineDyadicCell) ↦ regridChild A G half c := by
  have hA : Primrec fun p : RatIntervalCode × AffineDyadicCell ↦ p.1 := Primrec.fst
  have hc : Primrec fun p : RatIntervalCode × AffineDyadicCell ↦ p.2 := Primrec.snd
  have hself := (primrec_eligible G half).comp hA hc
  have hparent := (primrec_eligible G half).comp hA (primrec_affineDyadicCell_parent.comp hc)
  have hroot := Primrec.not.comp (primrec_affineDyadicCell_hasParent.comp hc)
  have hmax := Primrec.or.comp hroot (Primrec.not.comp hparent)
  exact (Primrec.and.comp hself hmax).of_eq fun _ ↦ rfl

theorem primrec_regridChild_cell (A : RatIntervalCode) (G : AffineDyadicGrid) (half : Bool) :
    Primrec (regridChild A G half) :=
  (primrec_regridChild G half).comp (Primrec.const A) Primrec.id

/-! ## Comparability at a non-rational point

Two cells containing a common non-rational point are related by refinement. Blocks must agree,
because distinct blocks meet only at a shared affine endpoint, which is rational; and within a
block the two words are both prefixes of any expansion of the normalized point. -/

private theorem rat_of_affine (G : AffineDyadicGrid) (r : ℚ) :
    ∃ s : ℚ, G.scale * (r : ℝ) + G.shift = (s : ℝ) := by
  refine ⟨((NNRatCode.value G.scaleCode : ℚ≥0) : ℚ) * r + RatCode.value G.shiftCode, ?_⟩
  rw [AffineDyadicGrid.scale, AffineDyadicGrid.shift]
  push_cast
  ring

private theorem mem_dyadicInterval_of_mem_cellInterval {G : AffineDyadicGrid}
    {c : AffineDyadicCell} {x : ℝ} (h : x ∈ G.cellInterval c) :
    (x - G.shift) / G.scale - (c.block : ℝ) ∈ dyadicInterval c.word := by
  have hs := G.zero_lt_scale
  rw [AffineDyadicGrid.cellInterval, Set.mem_Icc, AffineDyadicGrid.cellRight,
    AffineDyadicGrid.cellLeft, AffineDyadicGrid.cellWidth] at h
  rw [dyadicInterval, Set.mem_Icc, dyadicRight]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hs]
    nlinarith [h.1]
  · rw [sub_le_iff_le_add, div_le_iff₀ hs]
    nlinarith [h.2]

private theorem block_eq_of_mem_cellIntervals_of_ne_rat {G : AffineDyadicGrid}
    {c d : AffineDyadicCell} {x : ℝ} (hx : ∀ q : ℚ, x ≠ (q : ℝ))
    (hc : x ∈ G.cellInterval c) (hd : x ∈ G.cellInterval d) : c.block = d.block := by
  have hroot : ∀ e : AffineDyadicCell, x ∈ G.cellInterval e →
      G.scale * (e.block : ℝ) + G.shift ≤ x ∧
        x ≤ G.scale * ((e.block : ℝ) + 1) + G.shift := by
    intro e he
    have hsub : G.cellInterval e ⊆ G.cellInterval ⟨e.block, []⟩ :=
      G.cellInterval_subset_of_refines ⟨rfl, List.nil_prefix⟩
    have h := hsub he
    rw [AffineDyadicGrid.cellInterval, Set.mem_Icc, AffineDyadicGrid.cellRight,
      AffineDyadicGrid.cellLeft, AffineDyadicGrid.cellWidth] at h
    simp only [dyadicLeft_nil, dyadicWidth_nil, add_zero, mul_one] at h
    exact ⟨h.1, by linarith [h.2]⟩
  obtain ⟨hc1, hc2⟩ := hroot c hc
  obtain ⟨hd1, hd2⟩ := hroot d hd
  by_contra hne
  have hs := G.zero_lt_scale
  rcases lt_or_gt_of_ne hne with h | h
  · have hle : (c.block : ℝ) + 1 ≤ (d.block : ℝ) := by exact_mod_cast h
    obtain ⟨s, hs'⟩ := rat_of_affine G ((c.block : ℚ) + 1)
    refine hx s ?_
    rw [← hs']
    push_cast
    nlinarith [hc2, hd1]
  · have hle : (d.block : ℝ) + 1 ≤ (c.block : ℝ) := by exact_mod_cast h
    obtain ⟨s, hs'⟩ := rat_of_affine G ((d.block : ℚ) + 1)
    refine hx s ?_
    rw [← hs']
    push_cast
    nlinarith [hd2, hc1]

/-- **Comparability.** Two cells sharing a non-rational point are nested. -/
theorem comparable_of_mem_cellIntervals_of_ne_rat {G : AffineDyadicGrid}
    {c d : AffineDyadicCell} {x : ℝ} (hx : ∀ q : ℚ, x ≠ (q : ℝ))
    (hc : x ∈ G.cellInterval c) (hd : x ∈ G.cellInterval d) :
    c.Refines d ∨ d.Refines c := by
  have hblock := block_eq_of_mem_cellIntervals_of_ne_rat hx hc hd
  have hs := G.zero_lt_scale
  set u : ℝ := (x - G.shift) / G.scale - (c.block : ℝ) with hu
  have hmemc : u ∈ dyadicInterval c.word := mem_dyadicInterval_of_mem_cellInterval hc
  have hmemd : u ∈ dyadicInterval d.word := by
    rw [hu, hblock]
    exact mem_dyadicInterval_of_mem_cellInterval hd
  have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := dyadicInterval_subset_unit c.word hmemc
  have hunr : ∀ q : ℚ, u ≠ (q : ℝ) := by
    intro q hq
    obtain ⟨s, hs'⟩ := rat_of_affine G (q + (c.block : ℚ))
    refine hx s ?_
    rw [← hs']
    rw [hu, sub_eq_iff_eq_add] at hq
    push_cast
    field_simp at hq
    linarith [hq]
  obtain ⟨w, hw⟩ := exists_realOf_eq hu01
  have hcw : initSeg w c.word.length = c.word := by
    refine initSeg_eq_of_mem_dyadicInterval_of_ne_rat ?_ ?_
    · rw [hw]; exact hmemc
    · rw [hw]; exact hunr
  have hdw : initSeg w d.word.length = d.word := by
    refine initSeg_eq_of_mem_dyadicInterval_of_ne_rat ?_ ?_
    · rw [hw]; exact hmemd
    · rw [hw]; exact hunr
  rcases le_total c.word.length d.word.length with hlen | hlen
  · refine Or.inl ⟨hblock, ?_⟩
    rw [← hcw, ← hdw]
    exact initSeg_prefix_of_le hlen
  · refine Or.inr ⟨hblock.symm, ?_⟩
    rw [← hcw, ← hdw]
    exact initSeg_prefix_of_le hlen

/-- **Distinct regridding children meet only in rationals.** -/
theorem regridChild_disjoint_of_ne_rat {A : RatIntervalCode} {G : AffineDyadicGrid} {half : Bool}
    {c d : AffineDyadicCell} (hc : regridChild A G half c = true)
    (hd : regridChild A G half d = true) {x : ℝ} (hx : ∀ q : ℚ, x ≠ (q : ℝ))
    (hxc : x ∈ G.cellInterval c) (hxd : x ∈ G.cellInterval d) : c = d := by
  rcases comparable_of_mem_cellIntervals_of_ne_rat hx hxc hxd with h | h
  · exact regridChild_eq_of_refines hc hd h
  · exact (regridChild_eq_of_refines hd hc h).symm

end AlgorithmicRandomness
