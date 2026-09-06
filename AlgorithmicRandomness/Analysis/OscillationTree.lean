/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.ComputableMonotone
import AlgorithmicRandomness.Analysis.OscillationParams
import AlgorithmicRandomness.Coding.ComputableFold

/-!
# The nodes of the oscillating construction

BMN's oscillating martingale (§4.1.4) is built on a tree of rational intervals, each carrying the
values of the constructed function at its two endpoints. A child's values are interpolated from
its parent's: proportionally to the strictified source `F = f + id` in the betting state, and
linearly in the waiting state. The interpolation history is kept as syntax, so that a node is a
finite object and both endpoint values are evaluated from the same parent values.

The exact semantics lives in `ℝ`; the coded evaluator approximates it. Strictification enters the
signatures: the construction is parameterized by `f`, and `F := f.addIdentity` is used internally,
because the approximation contract needs the quantitative bound `b - a ≤ F b - F a` and not merely
strict monotonicity.

The interpolation weight is kept as a function on all of `ℝ`, continuous and monotone on the parent
interval. Regridding coverage excludes rational points, so the continuity of the final function at
such points will be controlled through this function rather than through an infinite child path.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-! ## Interpolation syntax -/

/-- One interpolation instruction: the values at the endpoints of `target` are obtained from the
values at the endpoints of `parent`, by the rule of the named state. -/
structure OscInterpStep where
  /-- Source-proportional (`true`) or linear (`false`) interpolation. -/
  betting : Bool
  /-- The interval whose endpoint values are the current ones. -/
  parent : RatIntervalCode
  /-- The interval whose endpoint values are to be produced. -/
  target : RatIntervalCode

/-- An interpolation history, applied left to right from the root values `(0, 1)`. -/
abbrev OscValueExpr := List OscInterpStep

namespace OscInterpStep

/-- The encoding equivalence. -/
def equivProd : OscInterpStep ≃ Bool × RatIntervalCode × RatIntervalCode where
  toFun s := (s.betting, s.parent, s.target)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := fun ⟨_, _, _⟩ ↦ rfl
  right_inv := fun ⟨_, _, _⟩ ↦ rfl

instance : Primcodable OscInterpStep := Primcodable.ofEquiv _ equivProd

theorem primrec_betting : Primrec betting :=
  Primrec.fst.comp (Primrec.of_equiv (e := equivProd))

theorem primrec_parent : Primrec parent :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd)))

theorem primrec_target : Primrec target :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd)))

theorem primrec_mk : Primrec fun p : Bool × RatIntervalCode × RatIntervalCode ↦
    (⟨p.1, p.2.1, p.2.2⟩ : OscInterpStep) :=
  (Primrec.of_equiv_symm (e := equivProd)).of_eq fun _ ↦ rfl

/-- The rational validity guard: the parent is nondegenerate, lies in `[0, 1]`, and contains the
target. Generated histories satisfy it; on arbitrary syntax it keeps every denominator away from
zero. -/
def valid (s : OscInterpStep) : Bool :=
  NNRatCode.lt (NNRatCode.ofNat 0) s.parent.widthCode
    && RatCode.le (RatCode.ofNat 0) s.parent.leftCode
    && RatCode.le s.parent.rightCode (RatCode.ofNat 1)
    && RatCode.le s.parent.leftCode s.target.leftCode
    && RatCode.le s.target.rightCode s.parent.rightCode

theorem valid_iff (s : OscInterpStep) :
    s.valid = true ↔
      0 < s.parent.width ∧ 0 ≤ s.parent.left ∧ s.parent.right ≤ 1 ∧
        s.parent.left ≤ s.target.left ∧ s.target.right ≤ s.parent.right := by
  rw [valid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    NNRatCode.lt_iff, RatCode.le_iff, RatCode.le_iff, RatCode.le_iff, RatCode.le_iff,
    NNRatCode.value_ofNat, RatCode.value_ofNat, RatCode.value_ofNat, Nat.cast_zero, Nat.cast_one]
  have h1 : (0 : ℚ≥0) < NNRatCode.value s.parent.widthCode ↔ 0 < s.parent.width := by
    rw [RatIntervalCode.width]
    exact_mod_cast Iff.rfl
  have h2 : (0 : ℚ) ≤ RatCode.value s.parent.leftCode ↔ 0 ≤ s.parent.left := by
    rw [RatIntervalCode.left]
    exact_mod_cast Iff.rfl
  have h3 : RatCode.value s.parent.rightCode ≤ (1 : ℚ) ↔ s.parent.right ≤ 1 := by
    rw [← RatIntervalCode.value_rightCode]
    exact_mod_cast Iff.rfl
  have h4 : RatCode.value s.parent.leftCode ≤ RatCode.value s.target.leftCode ↔
      s.parent.left ≤ s.target.left := by
    rw [RatIntervalCode.left, RatIntervalCode.left]
    exact_mod_cast Iff.rfl
  have h5 : RatCode.value s.target.rightCode ≤ RatCode.value s.parent.rightCode ↔
      s.target.right ≤ s.parent.right := by
    rw [← RatIntervalCode.value_rightCode, ← RatIntervalCode.value_rightCode]
    exact_mod_cast Iff.rfl
  simp only [Nat.cast_zero, h1, h2, h3, h4, h5, and_assoc]

theorem primrec_valid : Primrec valid := by
  have hpar := primrec_ratIntervalCode_widthCode.comp primrec_parent
  have hpl := primrec_ratIntervalCode_leftCode.comp primrec_parent
  have hpr := primrec_ratIntervalCode_rightCode.comp primrec_parent
  have htl := primrec_ratIntervalCode_leftCode.comp primrec_target
  have htr := primrec_ratIntervalCode_rightCode.comp primrec_target
  have h1 := NNRatCode.primrec_lt.comp (Primrec.const (NNRatCode.ofNat 0)) hpar
  have h2 := RatCode.primrec_le.comp (Primrec.const (RatCode.ofNat 0)) hpl
  have h3 := RatCode.primrec_le.comp hpr (Primrec.const (RatCode.ofNat 1))
  have h4 := RatCode.primrec_le.comp hpl htl
  have h5 := RatCode.primrec_le.comp htr hpr
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp h1 h2) h3) h4)
    h5).of_eq fun _ ↦ rfl

end OscInterpStep

/-! ## Exact semantics

Throughout, `F := f.addIdentity.toFun`. -/

section Exact

variable (f : ComputableMonotone)

/-- The interpolation weight `θ` on the parent interval `A = [a, b]`: `(F t - F a) / (F b - F a)`
in the betting state, `(t - a) / (b - a)` in the waiting state. -/
noncomputable def interpWeight (betting : Bool) (A : RatIntervalCode) (t : ℝ) : ℝ :=
  if betting then
    (f.addIdentity.toFun t - f.addIdentity.toFun A.left)
      / (f.addIdentity.toFun A.right - f.addIdentity.toFun A.left)
  else (t - A.left) / A.width

/-- The interpolated value `H(t) = L + (R - L) θ(t)`. -/
noncomputable def interp (betting : Bool) (A : RatIntervalCode) (L R t : ℝ) : ℝ :=
  L + (R - L) * interpWeight f betting A t

/-- The source gap of a valid parent is at least its width, hence positive. -/
theorem width_le_addIdentity_gap {A : RatIntervalCode} (h0 : 0 ≤ A.left) (h1 : A.right ≤ 1) :
    A.width ≤ f.addIdentity.toFun A.right - f.addIdentity.toFun A.left := by
  have hw := A.width_nonneg
  have hab : A.left ≤ A.right := by rw [RatIntervalCode.right]; linarith
  have := f.sub_le_addIdentity_sub ⟨h0, by linarith⟩ ⟨by linarith, h1⟩ hab
  rw [RatIntervalCode.right] at this ⊢
  linarith

theorem interpWeight_left (betting : Bool) (A : RatIntervalCode) :
    interpWeight f betting A A.left = 0 := by
  rw [interpWeight]
  cases betting <;> simp

theorem interpWeight_right {A : RatIntervalCode} (betting : Bool) (hw : 0 < A.width)
    (h0 : 0 ≤ A.left) (h1 : A.right ≤ 1) : interpWeight f betting A A.right = 1 := by
  rw [interpWeight]
  cases betting
  · simp only [Bool.false_eq_true, if_false, RatIntervalCode.right, add_sub_cancel_left]
    exact div_self hw.ne'
  · simp only [if_true]
    exact div_self (by linarith [width_le_addIdentity_gap f h0 h1])

theorem interp_left (betting : Bool) (A : RatIntervalCode) (L R : ℝ) :
    interp f betting A L R A.left = L := by
  rw [interp, interpWeight_left, mul_zero, add_zero]

theorem interp_right {A : RatIntervalCode} (betting : Bool) (hw : 0 < A.width) (h0 : 0 ≤ A.left)
    (h1 : A.right ≤ 1) (L R : ℝ) : interp f betting A L R A.right = R := by
  rw [interp, interpWeight_right f betting hw h0 h1]
  ring

theorem continuous_interpWeight (betting : Bool) (A : RatIntervalCode) :
    Continuous (interpWeight f betting A) := by
  unfold interpWeight
  cases betting
  · simp only [Bool.false_eq_true, if_false]
    exact (continuous_id.sub continuous_const).div_const _
  · simp only [if_true]
    exact (f.addIdentity.continuous_toFun.sub continuous_const).div_const _

theorem continuous_interp (betting : Bool) (A : RatIntervalCode) (L R : ℝ) :
    Continuous (interp f betting A L R) :=
  continuous_const.add (continuous_const.mul (continuous_interpWeight f betting A))

theorem interpWeight_mono {A : RatIntervalCode} (betting : Bool) (hw : 0 < A.width)
    (h0 : 0 ≤ A.left) (h1 : A.right ≤ 1) {s t : ℝ} (hst : s ≤ t) :
    interpWeight f betting A s ≤ interpWeight f betting A t := by
  rw [interpWeight, interpWeight]
  cases betting
  · simp only [Bool.false_eq_true, if_false]
    exact div_le_div_of_nonneg_right (by linarith) hw.le
  · simp only [if_true]
    have hgap := width_le_addIdentity_gap f h0 h1
    exact div_le_div_of_nonneg_right (by linarith [f.addIdentity.monotone_toFun hst])
      (by linarith)

/-- On a valid parent the weight stays in `[0, 1]` over the parent interval. -/
theorem interpWeight_mem {A : RatIntervalCode} (betting : Bool) (hw : 0 < A.width)
    (h0 : 0 ≤ A.left) (h1 : A.right ≤ 1) {t : ℝ} (ht : t ∈ A.interval) :
    interpWeight f betting A t ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [← interpWeight_left f betting A]
    exact interpWeight_mono f betting hw h0 h1 ht.1
  · rw [← interpWeight_right f betting hw h0 h1]
    exact interpWeight_mono f betting hw h0 h1 ht.2

/-! ### The child-mass identities

With `g[·]` the difference of the two endpoint values, a betting step keeps `g[B] / F[B]` equal to
`g[A] / F[A]`, and a waiting step keeps `g[B] / |B|` equal to `g[A] / |A|`. Both are stated as
cross-multiplied equalities, which need no hypothesis beyond the nonvanishing denominator. -/

theorem interp_sub_interp (betting : Bool) (A : RatIntervalCode) (L R c d : ℝ) :
    interp f betting A L R d - interp f betting A L R c =
      (R - L) * (interpWeight f betting A d - interpWeight f betting A c) := by
  rw [interp, interp]
  ring

theorem mass_betting_step {A : RatIntervalCode} (hw : 0 < A.width) (h0 : 0 ≤ A.left)
    (h1 : A.right ≤ 1) (L R c d : ℝ) :
    (interp f true A L R d - interp f true A L R c)
        * (f.addIdentity.toFun A.right - f.addIdentity.toFun A.left)
      = (R - L) * (f.addIdentity.toFun d - f.addIdentity.toFun c) := by
  have hgap := width_le_addIdentity_gap f h0 h1
  have hpos : f.addIdentity.toFun A.right - f.addIdentity.toFun A.left ≠ 0 := by linarith
  rw [interp_sub_interp, interpWeight, interpWeight]
  simp only [if_true]
  field_simp
  ring

theorem mass_waiting_step {A : RatIntervalCode} (hw : 0 < A.width) (L R c d : ℝ) :
    (interp f false A L R d - interp f false A L R c) * A.width = (R - L) * (d - c) := by
  rw [interp_sub_interp, interpWeight, interpWeight]
  simp only [Bool.false_eq_true, if_false]
  field_simp
  ring

/-- Entering the waiting state on a child of at most half the width halves the mass. -/
theorem mass_le_half_of_width_le_half {A B : RatIntervalCode} (hw : 0 < A.width)
    (hhalf : 2 * B.width ≤ A.width) {L R : ℝ} (hLR : L ≤ R) :
    interp f false A L R B.right - interp f false A L R B.left ≤ (R - L) / 2 := by
  have h := mass_waiting_step f hw L R B.left B.right
  have hBr : B.right - B.left = B.width := by rw [RatIntervalCode.right]; ring
  rw [hBr] at h
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hRL : 0 ≤ R - L := by linarith
  have h2 : (interp f false A L R B.right - interp f false A L R B.left) * 2 * A.width
      ≤ (R - L) * A.width := by nlinarith [mul_le_mul_of_nonneg_left hhalf hRL]
  exact le_of_mul_le_mul_right h2 hw

/-! ### Histories -/

/-- Ordered endpoint values in `[0, 1]`: the invariant every history preserves. -/
def OrderedUnit (p : ℝ × ℝ) : Prop := 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1

/-- One instruction on a value pair. Invalid instructions are the identity. -/
noncomputable def OscInterpStep.apply (s : OscInterpStep) (p : ℝ × ℝ) : ℝ × ℝ :=
  if s.valid then
    (interp f s.betting s.parent p.1 p.2 s.target.left,
      interp f s.betting s.parent p.1 p.2 s.target.right)
  else p

/-- The value pair of a history, from the root values `(0, 1)`. -/
noncomputable def OscValueExpr.eval (e : OscValueExpr) : ℝ × ℝ :=
  e.foldl (fun p s ↦ s.apply f p) (0, 1)

@[simp] theorem OscValueExpr.eval_nil : OscValueExpr.eval f [] = (0, 1) := rfl

theorem OscValueExpr.eval_append_singleton (e : OscValueExpr) (s : OscInterpStep) :
    OscValueExpr.eval f (e ++ [s]) = s.apply f (OscValueExpr.eval f e) := by
  rw [OscValueExpr.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem OscInterpStep.apply_of_valid {s : OscInterpStep} (hs : s.valid = true) (p : ℝ × ℝ) :
    s.apply f p = (interp f s.betting s.parent p.1 p.2 s.target.left,
      interp f s.betting s.parent p.1 p.2 s.target.right) := by
  rw [OscInterpStep.apply, if_pos hs]

theorem OscInterpStep.apply_of_not_valid {s : OscInterpStep} (hs : ¬ s.valid = true) (p : ℝ × ℝ) :
    s.apply f p = p := by
  rw [OscInterpStep.apply, if_neg hs]

theorem OscInterpStep.orderedUnit_apply (s : OscInterpStep) {p : ℝ × ℝ} (hp : OrderedUnit p) :
    OrderedUnit (s.apply f p) := by
  by_cases hs : s.valid = true
  · rw [OscInterpStep.apply_of_valid f hs]
    obtain ⟨hw, h0, h1, hl, hr⟩ := (OscInterpStep.valid_iff s).mp hs
    obtain ⟨hp0, hp1, hp2⟩ := hp
    have htw := s.target.width_nonneg
    have htlr : s.target.left ≤ s.target.right := by rw [RatIntervalCode.right]; linarith
    have hml : s.target.left ∈ s.parent.interval := ⟨hl, by linarith⟩
    have hmr : s.target.right ∈ s.parent.interval := ⟨by linarith, hr⟩
    have hθl := interpWeight_mem f s.betting hw h0 h1 hml
    have hθr := interpWeight_mem f s.betting hw h0 h1 hmr
    have hθ := interpWeight_mono f s.betting hw h0 h1 htlr
    simp only [OrderedUnit, interp]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hθl.1]
    · nlinarith
    · nlinarith [hθr.2]
  · rw [OscInterpStep.apply_of_not_valid f hs]
    exact hp

theorem OscValueExpr.orderedUnit_eval (e : OscValueExpr) : OrderedUnit (OscValueExpr.eval f e) := by
  induction e using List.reverseRecOn with
  | nil => exact ⟨le_rfl, zero_le_one, le_rfl⟩
  | append_singleton e s ih =>
    rw [OscValueExpr.eval_append_singleton]
    exact OscInterpStep.orderedUnit_apply f s ih

end Exact

/-! ## The coded evaluator

Values are kept as nonnegative codes: a child value is the convex combination
`L̂ (1 - ŵ) + R̂ ŵ` of the parent values with the approximate weight `ŵ ∈ [0, 1]`, which keeps every
approximate value in `[0, 1]` without a separate clamp and makes the errors accumulate additively.
-/

namespace RatIntervalCode

/-- A precision `t` with `4 · 2⁻ᵗ ≤ |A| · 2⁻ʲ`, read off the denominator of the coded width. It
serves the interpolation weights, whose error is `4η / |A|`, and the slope sampler, whose error is
`2η / |A|`. -/
def precisionFor (A : RatIntervalCode) (j : ℕ) : ℕ := j + 2 + (A.widthCode.unpair.2 + 1)

theorem primrec_precisionFor : Primrec₂ precisionFor :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))
    (Primrec.succ.comp
      (Primrec.snd.comp (Primrec.unpair.comp (primrec_ratIntervalCode_widthCode.comp Primrec.fst))))

theorem precisionFor_spec {A : RatIntervalCode} (hw : 0 < A.width) (j : ℕ) :
    4 * (2⁻¹ : ℝ) ^ A.precisionFor j ≤ A.width * (2⁻¹ : ℝ) ^ j := by
  set n := A.widthCode.unpair.1 with hn
  set d := A.widthCode.unpair.2 with hd
  have hval : A.width = (n : ℝ) / ((d : ℝ) + 1) := by
    rw [RatIntervalCode.width, NNRatCode.value]
    push_cast
    rfl
  have hn1 : (1 : ℝ) ≤ n := by
    have hn0 : n ≠ 0 := by
      intro h
      rw [hval, h] at hw
      simp at hw
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow : ((d : ℝ) + 1) ≤ (2 : ℝ) ^ (d + 1) := by
    have := Nat.lt_two_pow_self (n := d + 1)
    exact_mod_cast this.le
  have h2 : (2⁻¹ : ℝ) ^ (d + 1) ≤ 1 / ((d : ℝ) + 1) := by
    rw [inv_pow, one_div]
    exact inv_anti₀ (by positivity) hpow
  rw [precisionFor, pow_add, pow_add, hval]
  have hd0 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hpj : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ j := by positivity
  calc 4 * ((2⁻¹ : ℝ) ^ j * (2⁻¹ : ℝ) ^ 2 * (2⁻¹ : ℝ) ^ (d + 1))
      = (2⁻¹ : ℝ) ^ j * (2⁻¹ : ℝ) ^ (d + 1) := by norm_num; ring
    _ ≤ (2⁻¹ : ℝ) ^ j * (1 / ((d : ℝ) + 1)) := mul_le_mul_of_nonneg_left h2 hpj
    _ ≤ (2⁻¹ : ℝ) ^ j * ((n : ℝ) / ((d : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hpj
        rw [one_div, div_eq_mul_inv]
        exact le_mul_of_one_le_left (by positivity) hn1
    _ = (n : ℝ) / ((d : ℝ) + 1) * (2⁻¹ : ℝ) ^ j := by ring

end RatIntervalCode

-- The strictified source is only ever used through its approximation API and its named
-- theorems; sealing it keeps definitional unfolding from reaching into its construction.
attribute [local irreducible] ComputableMonotone.addIdentity

namespace OscInterpStep

variable (f : ComputableMonotone)

/-- The approximate weight at the selected endpoint of the target, as a nonnegative code in
`[0, 1]`. In the betting state the source gap is stabilised by `max(|A|, F̂ b - F̂ a)`; in the
waiting state the weight is an exact rational. -/
noncomputable def weightCode (s : OscInterpStep) (right : Bool) (j : ℕ) : ℕ :=
  let t := s.parent.precisionFor j
  let e := bif right then s.target.rightCode else s.target.leftCode
  bif s.betting then
    let num := RatCode.sub (f.addIdentity.approxAtCode e t)
      (f.addIdentity.approxAtCode s.parent.leftCode t)
    let diff := RatCode.sub (f.addIdentity.approxAtCode s.parent.rightCode t)
      (f.addIdentity.approxAtCode s.parent.leftCode t)
    let den := bif RatCode.le (RatCode.ofNNRat s.parent.widthCode) diff then RatCode.toNNRat diff
      else s.parent.widthCode
    RatCode.clampUnit (RatCode.divNNRat num den)
  else RatCode.clampUnit (RatCode.divNNRat (RatCode.sub e s.parent.leftCode) s.parent.widthCode)

theorem computable_weightCode :
    Computable fun p : OscInterpStep × Bool × ℕ ↦ weightCode f p.1 p.2.1 p.2.2 := by
  have hs : Primrec fun p : OscInterpStep × Bool × ℕ ↦ p.1 := Primrec.fst
  have hright : Primrec fun p : OscInterpStep × Bool × ℕ ↦ p.2.1 := Primrec.fst.comp Primrec.snd
  have hj : Primrec fun p : OscInterpStep × Bool × ℕ ↦ p.2.2 := Primrec.snd.comp Primrec.snd
  have hpar := primrec_parent.comp hs
  have htar := primrec_target.comp hs
  have ht := RatIntervalCode.primrec_precisionFor.comp hpar hj
  have he := Primrec.cond hright (primrec_ratIntervalCode_rightCode.comp htar)
    (primrec_ratIntervalCode_leftCode.comp htar)
  have hpl := primrec_ratIntervalCode_leftCode.comp hpar
  have hpr := primrec_ratIntervalCode_rightCode.comp hpar
  have hpw := primrec_ratIntervalCode_widthCode.comp hpar
  have hFe := f.addIdentity.computable_approxAtCode.comp he.to_comp ht.to_comp
  have hFa := f.addIdentity.computable_approxAtCode.comp hpl.to_comp ht.to_comp
  have hFb := f.addIdentity.computable_approxAtCode.comp hpr.to_comp ht.to_comp
  have hnum := RatCode.primrec_sub.to_comp.comp hFe hFa
  have hdiff := RatCode.primrec_sub.to_comp.comp hFb hFa
  have htest := RatCode.primrec_le.to_comp.comp (RatCode.primrec_ofNNRat.comp hpw).to_comp hdiff
  have hden := Computable.cond htest (RatCode.primrec_toNNRat.to_comp.comp hdiff) hpw.to_comp
  have hbet := RatCode.primrec_clampUnit.to_comp.comp
    (RatCode.primrec_divNNRat.to_comp.comp hnum hden)
  have hwait := (RatCode.primrec_clampUnit.comp
    (RatCode.primrec_divNNRat.comp (RatCode.primrec_sub.comp he hpl) hpw)).to_comp
  exact (Computable.cond (primrec_betting.comp hs).to_comp hbet hwait).of_eq fun _ ↦ rfl

/-! ### The weight error -/

/-- Clamping onto `[0, 1]` does not move a point away from a value already in `[0, 1]`. -/
private theorem abs_clamp_sub_le {y θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    |max 0 (min 1 y) - θ| ≤ |y - θ| := by
  obtain ⟨h0, h1⟩ := hθ
  rcases le_total y 0 with hy0 | hy0
  · rw [min_eq_right (by linarith), max_eq_left hy0]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  rcases le_total 1 y with hy1 | hy1
  · rw [min_eq_left hy1, max_eq_right zero_le_one]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right hy1, max_eq_right hy0]

/-- The quotient estimate behind the betting weight: numerator and denominator each known to
within `2η`, the denominator at least `w` on both sides, the true quotient in `[0, 1]`. -/
private theorem abs_div_sub_div_le {N D N' D' w η : ℝ} (hw : 0 < w) (hD : w ≤ D) (hD' : w ≤ D')
    (hN : |N' - N| ≤ 2 * η) (hDD : |D' - D| ≤ 2 * η) (hN0 : 0 ≤ N) (hND : N ≤ D) :
    |N' / D' - N / D| ≤ 4 * η / w := by
  have hDpos : 0 < D := by linarith
  have hD'pos : 0 < D' := by linarith
  have hη : 0 ≤ η := by
    have := abs_nonneg (N' - N)
    linarith
  have hθ : N / D ≤ 1 := by rw [div_le_one hDpos]; exact hND
  have hθ0 : 0 ≤ N / D := div_nonneg hN0 hDpos.le
  have hsplit : N' / D' - N / D = (N' - N) / D' + (N / D) * ((D - D') / D') := by
    field_simp
    ring
  rw [hsplit]
  have h1 : |(N' - N) / D'| ≤ 2 * η / w := by
    rw [abs_div, abs_of_pos hD'pos]
    exact div_le_div₀ (by linarith) hN hw hD'
  have h2 : |(N / D) * ((D - D') / D')| ≤ 2 * η / w := by
    rw [abs_mul, abs_of_nonneg hθ0, abs_div, abs_of_pos hD'pos, abs_sub_comm]
    calc N / D * (|D' - D| / D') ≤ 1 * (2 * η / D') := by
          apply mul_le_mul hθ _ (by positivity) zero_le_one
          exact div_le_div_of_nonneg_right hDD hD'pos.le
      _ ≤ 2 * η / w := by
          rw [one_mul]
          exact div_le_div_of_nonneg_left (by linarith) hw hD'
  calc |(N' - N) / D' + N / D * ((D - D') / D')|
      ≤ |(N' - N) / D'| + |N / D * ((D - D') / D')| := abs_add_le _ _
    _ ≤ 2 * η / w + 2 * η / w := add_le_add h1 h2
    _ = 4 * η / w := by ring

/-- The endpoint named by the flag. -/
noncomputable def endpoint (s : OscInterpStep) (right : Bool) : ℝ :=
  if right then s.target.right else s.target.left

theorem value_endpointCode (s : OscInterpStep) (right : Bool) :
    ((RatCode.value (bif right then s.target.rightCode else s.target.leftCode) : ℚ) : ℝ)
      = s.endpoint right := by
  cases right
  · rfl
  · simp only [cond_true, endpoint, if_true]
    exact RatIntervalCode.value_rightCode _

theorem endpoint_mem {s : OscInterpStep} (hs : s.valid = true) (right : Bool) :
    s.endpoint right ∈ s.parent.interval := by
  obtain ⟨-, -, -, hl, hr⟩ := (valid_iff s).mp hs
  have htw := s.target.width_nonneg
  have htlr : s.target.left ≤ s.target.right := by rw [RatIntervalCode.right]; linarith
  cases right
  · exact ⟨hl, by simpa [endpoint] using le_trans htlr hr⟩
  · exact ⟨by simpa [endpoint] using le_trans hl htlr, hr⟩

theorem weight_error {s : OscInterpStep} (hs : s.valid = true) (right : Bool) (j : ℕ) :
    |((NNRatCode.value (s.weightCode f right j) : ℚ) : ℝ)
        - interpWeight f s.betting s.parent (s.endpoint right)| ≤ (2⁻¹ : ℝ) ^ j := by
  obtain ⟨hw, h0, h1, -, -⟩ := (valid_iff s).mp hs
  have hwq : 0 < NNRatCode.value s.parent.widthCode := by
    rw [RatIntervalCode.width] at hw
    exact_mod_cast hw
  have hθ := interpWeight_mem f s.betting hw h0 h1 (endpoint_mem hs right)
  set t := s.parent.precisionFor j with ht
  have hprec := RatIntervalCode.precisionFor_spec hw j
  rw [← ht] at hprec
  set η : ℝ := (2⁻¹ : ℝ) ^ t with hη
  have hx := value_endpointCode s right
  -- the exact values of the three coded endpoints
  have hxa : ((RatCode.value s.parent.leftCode : ℚ) : ℝ) = s.parent.left := rfl
  have hxb : ((RatCode.value s.parent.rightCode : ℚ) : ℝ) = s.parent.right :=
    RatIntervalCode.value_rightCode _
  cases hb : s.betting
  · -- waiting: the exact rational weight, clamped
    have hval : ((NNRatCode.value (s.weightCode f right j) : ℚ) : ℝ)
        = max 0 (min 1 ((s.endpoint right - s.parent.left) / s.parent.width)) := by
      simp only [weightCode, hb, cond_false]
      rw [RatCode.value_clampUnit, RatCode.value_divNNRat hwq, RatCode.value_sub]
      push_cast
      rw [hx, hxa, RatIntervalCode.width]
    rw [hval, interpWeight] at *
    simp only [hb, Bool.false_eq_true, if_false] at hθ ⊢
    rw [min_eq_right hθ.2, max_eq_right hθ.1, sub_self, abs_zero]
    positivity
  · -- betting: the stabilised quotient, clamped
    have hgap := width_le_addIdentity_gap f h0 h1
    have hmem := endpoint_mem hs right
    have hmono1 := f.addIdentity.monotone_toFun hmem.1
    have hmono2 := f.addIdentity.monotone_toFun hmem.2
    have hθ' : interpWeight f true s.parent (s.endpoint right)
        = (f.addIdentity.toFun (s.endpoint right) - f.addIdentity.toFun s.parent.left)
          / (f.addIdentity.toFun s.parent.right - f.addIdentity.toFun s.parent.left) := by
      rw [interpWeight, if_pos rfl]
    rw [hb, hθ'] at hθ
    have hFa := f.addIdentity.abs_toFun_sub_approxAt_le s.parent.leftCode t
    have hFb := f.addIdentity.abs_toFun_sub_approxAt_le s.parent.rightCode t
    have hFx := f.addIdentity.abs_toFun_sub_approxAt_le
      (bif right then s.target.rightCode else s.target.leftCode) t
    rw [hxa] at hFa
    rw [hxb] at hFb
    rw [hx] at hFx
    -- the coded denominator evaluates to `max |A| (F̂ b - F̂ a)`
    have hden : ∀ diff : ℕ,
        ((NNRatCode.value (bif RatCode.le (RatCode.ofNNRat s.parent.widthCode) diff then
          RatCode.toNNRat diff else s.parent.widthCode) : ℚ) : ℝ)
          = max s.parent.width ((RatCode.value diff : ℚ) : ℝ) := by
      intro diff
      by_cases hle : RatCode.le (RatCode.ofNNRat s.parent.widthCode) diff = true
      · rw [hle, cond_true]
        have hle' := (RatCode.le_iff _ _).mp hle
        rw [RatCode.value_ofNNRat] at hle'
        rw [RatCode.value_toNNRat (le_trans (by positivity) hle')]
        rw [max_eq_right]
        rw [RatIntervalCode.width]
        exact_mod_cast hle'
      · rw [Bool.eq_false_iff.mpr hle, cond_false]
        have hlt : RatCode.value diff < NNRatCode.value s.parent.widthCode := by
          rw [RatCode.le_iff, RatCode.value_ofNNRat] at hle
          exact not_le.mp hle
        rw [max_eq_left]
        · rfl
        · rw [RatIntervalCode.width]
          exact_mod_cast hlt.le
    have hval : ((NNRatCode.value (s.weightCode f right j) : ℚ) : ℝ)
        = max 0 (min 1
          ((((f.addIdentity.approxAt (bif right then s.target.rightCode else s.target.leftCode) t
              : ℚ) : ℝ) - ((f.addIdentity.approxAt s.parent.leftCode t : ℚ) : ℝ))
            / max s.parent.width (((f.addIdentity.approxAt s.parent.rightCode t : ℚ) : ℝ)
              - ((f.addIdentity.approxAt s.parent.leftCode t : ℚ) : ℝ)))) := by
      simp only [weightCode, hb, cond_true]
      have hdpos : 0 < NNRatCode.value (bif RatCode.le (RatCode.ofNNRat s.parent.widthCode)
          (RatCode.sub (f.addIdentity.approxAtCode s.parent.rightCode t)
            (f.addIdentity.approxAtCode s.parent.leftCode t)) then
          RatCode.toNNRat (RatCode.sub (f.addIdentity.approxAtCode s.parent.rightCode t)
            (f.addIdentity.approxAtCode s.parent.leftCode t)) else s.parent.widthCode) := by
        have h := hden (RatCode.sub (f.addIdentity.approxAtCode s.parent.rightCode t)
          (f.addIdentity.approxAtCode s.parent.leftCode t))
        have : (0 : ℝ) < ((NNRatCode.value (bif RatCode.le (RatCode.ofNNRat s.parent.widthCode)
            (RatCode.sub (f.addIdentity.approxAtCode s.parent.rightCode t)
              (f.addIdentity.approxAtCode s.parent.leftCode t)) then
            RatCode.toNNRat (RatCode.sub (f.addIdentity.approxAtCode s.parent.rightCode t)
              (f.addIdentity.approxAtCode s.parent.leftCode t))
            else s.parent.widthCode) : ℚ) : ℝ) := by
          rw [h]
          exact lt_max_of_lt_left hw
        exact_mod_cast this
      rw [RatCode.value_clampUnit, RatCode.value_divNNRat hdpos, Rat.cast_max, Rat.cast_min,
        Rat.cast_div, Rat.cast_zero, Rat.cast_one, hden, RatCode.value_sub, RatCode.value_sub]
      push_cast
      rfl
    set Fa := f.addIdentity.toFun s.parent.left with hFa_def
    set Fb := f.addIdentity.toFun s.parent.right with hFb_def
    set Fx := f.addIdentity.toFun (s.endpoint right) with hFx_def
    set Fa' : ℝ := ((f.addIdentity.approxAt s.parent.leftCode t : ℚ) : ℝ) with hFa'_def
    set Fb' : ℝ := ((f.addIdentity.approxAt s.parent.rightCode t : ℚ) : ℝ) with hFb'_def
    set Fx' : ℝ := ((f.addIdentity.approxAt
      (bif right then s.target.rightCode else s.target.leftCode) t : ℚ) : ℝ) with hFx'_def
    clear_value Fa Fb Fx Fa' Fb' Fx'
    rw [hval, hθ']
    refine le_trans (abs_clamp_sub_le hθ) ?_
    have hN : |(Fx' - Fa') - (Fx - Fa)| ≤ 2 * η := by
      rw [abs_sub_comm] at hFx hFa
      calc |(Fx' - Fa') - (Fx - Fa)| = |(Fx' - Fx) + (Fa - Fa')| := by
            rw [show (Fx' - Fa') - (Fx - Fa) = (Fx' - Fx) + (Fa - Fa') by ring]
        _ ≤ |Fx' - Fx| + |Fa - Fa'| := abs_add_le _ _
        _ ≤ η + η := add_le_add hFx (by rwa [abs_sub_comm])
        _ = 2 * η := by ring
    have hD0 : |(Fb' - Fa') - (Fb - Fa)| ≤ 2 * η := by
      rw [abs_sub_comm] at hFb hFa
      calc |(Fb' - Fa') - (Fb - Fa)| = |(Fb' - Fb) + (Fa - Fa')| := by
            rw [show (Fb' - Fa') - (Fb - Fa) = (Fb' - Fb) + (Fa - Fa') by ring]
        _ ≤ |Fb' - Fb| + |Fa - Fa'| := abs_add_le _ _
        _ ≤ η + η := add_le_add hFb (by rwa [abs_sub_comm])
        _ = 2 * η := by ring
    have hDD : |max s.parent.width (Fb' - Fa') - (Fb - Fa)| ≤ 2 * η := by
      have hmax : max s.parent.width (Fb - Fa) = Fb - Fa := max_eq_right hgap
      calc |max s.parent.width (Fb' - Fa') - (Fb - Fa)|
          = |max s.parent.width (Fb' - Fa') - max s.parent.width (Fb - Fa)| := by rw [hmax]
        _ ≤ max |s.parent.width - s.parent.width| |(Fb' - Fa') - (Fb - Fa)| :=
            abs_max_sub_max_le_max _ _ _ _
        _ ≤ 2 * η := by
            rw [sub_self, abs_zero]
            exact max_le (by positivity) hD0
    have hN0 : 0 ≤ Fx - Fa := by linarith
    have hND : Fx - Fa ≤ Fb - Fa := by linarith
    refine le_trans (abs_div_sub_div_le hw hgap (le_max_left _ _) hN hDD hN0 hND) ?_
    rw [div_le_iff₀ hw]
    linarith

theorem value_weightCode_le_one (s : OscInterpStep) (right : Bool) (j : ℕ) :
    NNRatCode.value (s.weightCode f right j) ≤ 1 := by
  have h : ∀ m : ℕ, NNRatCode.value (RatCode.clampUnit m) ≤ 1 := fun m ↦ by
    have h : ((NNRatCode.value (RatCode.clampUnit m) : ℚ≥0) : ℚ) ≤ 1 := by
      rw [RatCode.value_clampUnit]
      exact max_le zero_le_one (min_le_left _ _)
    exact_mod_cast h
  cases hb : s.betting <;> simp only [weightCode, hb, cond_true, cond_false] <;> exact h _

end OscInterpStep

-- The weight is used only through its computability, its error, and its bound; sealing it keeps
-- every later definitional check from reaching into the approximation program.
attribute [local irreducible] OscInterpStep.weightCode

/-! ### Pair evaluation -/

namespace OscInterpStep

variable (f : ComputableMonotone)

/-- The convex combination `L̂ (1 - ŵ) + R̂ ŵ`, on nonnegative codes. -/
def mixCode (L R w : ℕ) : ℕ :=
  NNRatCode.add (NNRatCode.mul L (NNRatCode.sub (NNRatCode.ofNat 1) w)) (NNRatCode.mul R w)

theorem primrec_mixCode : Primrec fun p : ℕ × ℕ × ℕ ↦ mixCode p.1 p.2.1 p.2.2 :=
  NNRatCode.primrec_add.comp
    (NNRatCode.primrec_mul.comp Primrec.fst
      (NNRatCode.primrec_sub.comp (Primrec.const (NNRatCode.ofNat 1))
        (Primrec.snd.comp Primrec.snd)))
    (NNRatCode.primrec_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem value_mixCode {L R w : ℕ} (hw : NNRatCode.value w ≤ 1) :
    ((NNRatCode.value (mixCode L R w) : ℚ) : ℝ)
      = ((NNRatCode.value L : ℚ) : ℝ) * (1 - ((NNRatCode.value w : ℚ) : ℝ))
        + ((NNRatCode.value R : ℚ) : ℝ) * ((NNRatCode.value w : ℚ) : ℝ) := by
  rw [mixCode, NNRatCode.value_add, NNRatCode.value_mul, NNRatCode.value_mul, NNRatCode.value_sub,
    NNRatCode.value_ofNat, Nat.cast_one]
  push_cast [NNRat.coe_sub hw]
  ring

-- Sealed for the same reason as the weight: its value theorem is its whole interface.
attribute [local irreducible] mixCode

/-- One instruction on a coded pair at weight precision `j`. Invalid instructions are skipped,
exactly as in the exact semantics. -/
noncomputable def applyCode (s : OscInterpStep) (j : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  bif s.valid then
    (mixCode p.1 p.2 (s.weightCode f false j), mixCode p.1 p.2 (s.weightCode f true j))
  else p

theorem computable_applyCode :
    Computable fun q : OscInterpStep × ℕ × ℕ × ℕ ↦ applyCode f q.1 q.2.1 q.2.2 := by
  have hs : Primrec fun q : OscInterpStep × ℕ × ℕ × ℕ ↦ q.1 := Primrec.fst
  have hj : Primrec fun q : OscInterpStep × ℕ × ℕ × ℕ ↦ q.2.1 := Primrec.fst.comp Primrec.snd
  have hp : Primrec fun q : OscInterpStep × ℕ × ℕ × ℕ ↦ q.2.2 := Primrec.snd.comp Primrec.snd
  have hwl : Computable fun q : OscInterpStep × ℕ × ℕ × ℕ ↦ q.1.weightCode f false q.2.1 :=
    ((computable_weightCode f).comp (hs.pair ((Primrec.const false).pair hj)).to_comp).of_eq
      fun _ ↦ rfl
  have hwr : Computable fun q : OscInterpStep × ℕ × ℕ × ℕ ↦ q.1.weightCode f true q.2.1 :=
    ((computable_weightCode f).comp (hs.pair ((Primrec.const true).pair hj)).to_comp).of_eq
      fun _ ↦ rfl
  have hmix : ∀ {w : OscInterpStep × ℕ × ℕ × ℕ → ℕ}, Computable w →
      Computable fun q : OscInterpStep × ℕ × ℕ × ℕ ↦ mixCode q.2.2.1 q.2.2.2 (w q) :=
    fun hw ↦ primrec_mixCode.to_comp.comp
      ((Primrec.fst.comp hp).to_comp.pair ((Primrec.snd.comp hp).to_comp.pair hw))
  exact (Computable.cond (primrec_valid.comp hs).to_comp ((hmix hwl).pair (hmix hwr))
    hp.to_comp).of_eq fun _ ↦ rfl

theorem applyCode_of_valid {s : OscInterpStep} (hs : s.valid = true) (j : ℕ) (p : ℕ × ℕ) :
    s.applyCode f j p
      = (mixCode p.1 p.2 (s.weightCode f false j), mixCode p.1 p.2 (s.weightCode f true j)) := by
  rw [applyCode, hs, cond_true]

theorem applyCode_of_not_valid {s : OscInterpStep} (hs : ¬ s.valid = true) (j : ℕ) (p : ℕ × ℕ) :
    s.applyCode f j p = p := by
  rw [applyCode, Bool.eq_false_iff.mpr hs, cond_false]

end OscInterpStep

attribute [local irreducible] OscInterpStep.applyCode

namespace OscValueExpr

variable (f : ComputableMonotone)

/-- The coded value pair of a history, to within `2⁻ᵏ`: every instruction uses weight precision
`k + length + 1`, so the additive errors sum to at most `2⁻ᵏ`. -/
noncomputable def evalCode (e : OscValueExpr) (k : ℕ) : ℕ × ℕ :=
  e.foldl (fun p s ↦ s.applyCode f (k + e.length + 1) p) (NNRatCode.ofNat 0, NNRatCode.ofNat 1)

theorem computable_evalCode : Computable₂ (evalCode f) := by
  have hlist : Computable fun q : OscValueExpr × ℕ ↦ q.1 := Computable.fst
  have hroot : Computable fun _ : OscValueExpr × ℕ ↦ (NNRatCode.ofNat 0, NNRatCode.ofNat 1) :=
    Computable.const _
  have hprec : Computable fun q : OscValueExpr × ℕ ↦ q.2 + q.1.length + 1 :=
    (Primrec.succ.comp (Primrec.nat_add.comp Primrec.snd
      (Primrec.list_length.comp Primrec.fst))).to_comp
  have hstep : Computable₂ fun (q : OscValueExpr × ℕ) (r : (ℕ × ℕ) × OscInterpStep) ↦
      r.2.applyCode f (q.2 + q.1.length + 1) r.1 :=
    ((OscInterpStep.computable_applyCode f).comp
      ((Computable.snd.comp Computable.snd).pair
        ((hprec.comp Computable.fst).pair (Computable.fst.comp Computable.snd)))).of_eq
      fun _ ↦ rfl
  exact (Computable.list_foldl hlist hroot hstep).of_eq fun _ ↦ rfl

/-! ### The error contract -/

/-- Both coded values in `[0, 1]`, each within `ε` of its exact counterpart. -/
def Approx (p : ℕ × ℕ) (q : ℝ × ℝ) (ε : ℝ) : Prop :=
  NNRatCode.value p.1 ≤ 1 ∧ NNRatCode.value p.2 ≤ 1 ∧
    |((NNRatCode.value p.1 : ℚ) : ℝ) - q.1| ≤ ε ∧ |((NNRatCode.value p.2 : ℚ) : ℝ) - q.2| ≤ ε

theorem Approx.mono {p : ℕ × ℕ} {q : ℝ × ℝ} {ε ε' : ℝ} (h : Approx p q ε) (hle : ε ≤ ε') :
    Approx p q ε' :=
  ⟨h.1, h.2.1, le_trans h.2.2.1 hle, le_trans h.2.2.2 hle⟩

/-- The one-step estimate: a weight within `δ` produces a value within `ε + δ`. -/
private theorem abs_mix_sub_le {L R L' R' θ w ε δ : ℝ} (hL : |L' - L| ≤ ε) (hR : |R' - R| ≤ ε)
    (hθ : |w - θ| ≤ δ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hLR : L ≤ R) (hRL : R - L ≤ 1) :
    |(L' * (1 - w) + R' * w) - (L + (R - L) * θ)| ≤ ε + δ := by
  have h : (L' * (1 - w) + R' * w) - (L + (R - L) * θ)
      = (L' - L) * (1 - w) + (R' - R) * w + (R - L) * (w - θ) := by ring
  rw [h]
  have h1 : |(L' - L) * (1 - w)| ≤ ε * (1 - w) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - w)]
    exact mul_le_mul_of_nonneg_right hL (by linarith)
  have h2 : |(R' - R) * w| ≤ ε * w := by
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right hR hw0
  have h3 : |(R - L) * (w - θ)| ≤ δ := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R - L)]
    calc (R - L) * |w - θ| ≤ 1 * δ :=
          mul_le_mul hRL hθ (abs_nonneg _) zero_le_one
      _ = δ := one_mul _
  calc |(L' - L) * (1 - w) + (R' - R) * w + (R - L) * (w - θ)|
      ≤ |(L' - L) * (1 - w) + (R' - R) * w| + |(R - L) * (w - θ)| := abs_add_le _ _
    _ ≤ (|(L' - L) * (1 - w)| + |(R' - R) * w|) + |(R - L) * (w - θ)| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (ε * (1 - w) + ε * w) + δ := add_le_add (add_le_add h1 h2) h3
    _ = ε + δ := by ring

theorem approx_applyCode (s : OscInterpStep) (j : ℕ) {p : ℕ × ℕ} {q : ℝ × ℝ}
    {ε : ℝ} (hq : OrderedUnit q) (h : Approx p q ε) :
    Approx (s.applyCode f j p) (s.apply f q) (ε + (2⁻¹ : ℝ) ^ j) := by
  obtain ⟨hp1, hp2, he1, he2⟩ := h
  obtain ⟨hq0, hq12, hq1⟩ := hq
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) he1
  by_cases hs : s.valid = true
  · rw [OscInterpStep.applyCode_of_valid f hs, OscInterpStep.apply_of_valid f hs]
    have hclamp : ∀ right : Bool, NNRatCode.value (s.weightCode f right j) ≤ 1 :=
      fun right ↦ OscInterpStep.value_weightCode_le_one f s right j
    have hstep : ∀ right : Bool,
        NNRatCode.value (OscInterpStep.mixCode p.1 p.2 (s.weightCode f right j)) ≤ 1 ∧
        |((NNRatCode.value (OscInterpStep.mixCode p.1 p.2 (s.weightCode f right j)) : ℚ) : ℝ)
          - interp f s.betting s.parent q.1 q.2 (s.endpoint right)| ≤ ε + (2⁻¹ : ℝ) ^ j := by
      intro right
      have hwle := hclamp right
      have hwr : ((NNRatCode.value (s.weightCode f right j) : ℚ) : ℝ) ≤ 1 := by
        exact_mod_cast hwle
      have hw0 : (0 : ℝ) ≤ ((NNRatCode.value (s.weightCode f right j) : ℚ) : ℝ) := by
        positivity
      have herr := OscInterpStep.weight_error f hs right j
      have hp1' : ((NNRatCode.value p.1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hp1
      have hp2' : ((NNRatCode.value p.2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hp2
      rw [OscInterpStep.value_mixCode hwle]
      have hp1'' : (0 : ℝ) ≤ ((NNRatCode.value p.1 : ℚ) : ℝ) := by positivity
      have hp2'' : (0 : ℝ) ≤ ((NNRatCode.value p.2 : ℚ) : ℝ) := by positivity
      have hle : ((NNRatCode.value (OscInterpStep.mixCode p.1 p.2 (s.weightCode f right j)) : ℚ)
          : ℝ) ≤ 1 := by
        rw [OscInterpStep.value_mixCode hwle]
        nlinarith
      refine ⟨by exact_mod_cast hle, ?_⟩
      rw [interp]
      exact abs_mix_sub_le he1 he2 herr hw0 hwr hq12 (by linarith)
    have hl := hstep false
    have hr := hstep true
    rw [show s.endpoint false = s.target.left from rfl] at hl
    rw [show s.endpoint true = s.target.right from rfl] at hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hl.1
    · dsimp only
      exact hr.1
    · dsimp only
      exact hl.2
    · dsimp only
      exact hr.2
  · rw [OscInterpStep.applyCode_of_not_valid f hs, OscInterpStep.apply_of_not_valid f hs]
    have hj : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ j := by positivity
    exact ⟨hp1, hp2, le_trans he1 (by linarith), le_trans he2 (by linarith)⟩

/-- The fold from an approximate pair, over any suffix of instructions. -/
private theorem approx_foldl (l : List OscInterpStep) (j : ℕ) :
    ∀ {p : ℕ × ℕ} {q : ℝ × ℝ} {ε : ℝ}, OrderedUnit q → Approx p q ε →
      Approx (l.foldl (fun p s ↦ s.applyCode f j p) p) (l.foldl (fun q s ↦ s.apply f q) q)
        (ε + l.length * (2⁻¹ : ℝ) ^ j) := by
  induction l with
  | nil =>
    intro p q ε _ h
    simpa using h
  | cons s l ih =>
    intro p q ε hq h
    rw [List.foldl_cons, List.foldl_cons]
    have := ih (OscInterpStep.orderedUnit_apply f s hq) (approx_applyCode f s j hq h)
    refine this.mono (le_of_eq ?_)
    rw [List.length_cons]
    push_cast
    ring

theorem approx_evalCode (e : OscValueExpr) (k : ℕ) :
    Approx (evalCode f e k) (eval f e) ((2⁻¹ : ℝ) ^ k) := by
  have hroot : Approx (NNRatCode.ofNat 0, NNRatCode.ofNat 1) ((0 : ℝ), (1 : ℝ)) 0 := by
    refine ⟨by simp, by simp, ?_, ?_⟩ <;> simp
  have h := approx_foldl f e (k + e.length + 1) ⟨le_rfl, zero_le_one, le_rfl⟩ hroot
  rw [zero_add] at h
  refine h.mono ?_
  have hlen : (e.length : ℝ) ≤ 2 ^ (e.length + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := e.length)).le.trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
  have hpn : (0 : ℝ) < (2 : ℝ) ^ (e.length + 1) := by positivity
  have hsmall : (e.length : ℝ) * (2⁻¹ : ℝ) ^ (e.length + 1) ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one hpn]
    exact hlen
  calc (e.length : ℝ) * (2⁻¹ : ℝ) ^ (k + e.length + 1)
      = (2⁻¹ : ℝ) ^ k * ((e.length : ℝ) * (2⁻¹ : ℝ) ^ (e.length + 1)) := by ring
    _ ≤ (2⁻¹ : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (2⁻¹ : ℝ) ^ k := mul_one _

end OscValueExpr

/-! ## Raw nodes

A node carries its interval, its interpolation history, its state, the grid cell it occupies
(`none` at the root, before the first regridding), and the frame at which the current phase was
entered. The anchor has one consumer: the phase-ratio invariant of the next checkpoint compares a
node's mass with its anchor's. It is reset on a switch, before the regridding child is selected,
and preserved by ordinary subdivision. -/

/-- An interval with its endpoint values. -/
structure OscFrame where
  /-- The interval. -/
  interval : RatIntervalCode
  /-- The history evaluating to the endpoint values. -/
  values : OscValueExpr

/-- A raw node of the construction. Validity is an invariant of use, not a field. -/
structure OscNode extends OscFrame where
  /-- The current state. -/
  betting : Bool
  /-- The grid cell, once regridded. -/
  cell : Option AffineDyadicCell
  /-- The frame at which the current phase was entered. -/
  phaseStart : OscFrame

namespace OscFrame

/-- The encoding equivalence. -/
def equivProd : OscFrame ≃ RatIntervalCode × OscValueExpr where
  toFun F := (F.interval, F.values)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

instance : Primcodable OscFrame := Primcodable.ofEquiv _ equivProd

theorem primrec_interval : Primrec interval :=
  Primrec.fst.comp (Primrec.of_equiv (e := equivProd))

theorem primrec_values : Primrec values :=
  Primrec.snd.comp (Primrec.of_equiv (e := equivProd))

theorem primrec_mk : Primrec fun p : RatIntervalCode × OscValueExpr ↦ (⟨p.1, p.2⟩ : OscFrame) :=
  (Primrec.of_equiv_symm (e := equivProd)).of_eq fun _ ↦ rfl

/-- The root frame: the unit interval with the empty history. -/
def root : OscFrame := ⟨RatIntervalCode.unit, []⟩

end OscFrame

namespace OscNode

/-- The encoding equivalence. -/
def equivProd : OscNode ≃ OscFrame × Bool × Option AffineDyadicCell × OscFrame where
  toFun n := (n.toOscFrame, n.betting, n.cell, n.phaseStart)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ ↦ rfl
  right_inv := fun ⟨_, _, _, _⟩ ↦ rfl

instance : Primcodable OscNode := Primcodable.ofEquiv _ equivProd

theorem primrec_toOscFrame : Primrec toOscFrame :=
  Primrec.fst.comp (Primrec.of_equiv (e := equivProd))

theorem primrec_betting : Primrec betting :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd)))

theorem primrec_cell : Primrec cell :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd))))

theorem primrec_phaseStart : Primrec phaseStart :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd))))

theorem primrec_mk :
    Primrec fun p : OscFrame × Bool × Option AffineDyadicCell × OscFrame ↦
      (⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ : OscNode) :=
  (Primrec.of_equiv_symm (e := equivProd)).of_eq fun _ ↦ rfl

theorem primrec_interval : Primrec fun n : OscNode ↦ n.interval :=
  OscFrame.primrec_interval.comp primrec_toOscFrame

theorem primrec_values : Primrec fun n : OscNode ↦ n.values :=
  OscFrame.primrec_values.comp primrec_toOscFrame

/-- The root: the unit interval, empty history, betting, not yet regridded, anchored at itself. -/
def root : OscNode := ⟨OscFrame.root, true, none, OscFrame.root⟩

variable (f : ComputableMonotone) (P : OscillationParams)

/-- The signed slope of the strictified source over the node's interval, sampled to within the
parameters' margin. -/
noncomputable def slopeCode (n : OscNode) : ℕ :=
  let t := n.interval.precisionFor P.precision
  RatCode.divNNRat
    (RatCode.sub (f.addIdentity.approxAtCode n.interval.rightCode t)
      (f.addIdentity.approxAtCode n.interval.leftCode t))
    n.interval.widthCode

theorem computable_slopeCode : Computable (slopeCode f P) := by
  have hI := primrec_interval
  have ht := RatIntervalCode.primrec_precisionFor.comp hI (Primrec.const P.precision)
  have hR := f.addIdentity.computable_approxAtCode.comp
    (primrec_ratIntervalCode_rightCode.comp hI).to_comp ht.to_comp
  have hL := f.addIdentity.computable_approxAtCode.comp
    (primrec_ratIntervalCode_leftCode.comp hI).to_comp ht.to_comp
  exact (RatCode.primrec_divNNRat.to_comp.comp (RatCode.primrec_sub.to_comp.comp hR hL)
    (primrec_ratIntervalCode_widthCode.comp hI).to_comp).of_eq fun _ ↦ rfl

theorem slopeCode_error (n : OscNode) (hw : 0 < n.interval.width) :
    |((RatCode.value (slopeCode f P n) : ℚ) : ℝ)
        - slope f.addIdentity.toFun n.interval.left n.interval.right| ≤ P.margin := by
  have hwq : 0 < NNRatCode.value n.interval.widthCode := by
    rw [RatIntervalCode.width] at hw
    exact_mod_cast hw
  set t := n.interval.precisionFor P.precision with ht
  have hprec := RatIntervalCode.precisionFor_spec hw P.precision
  rw [← ht] at hprec
  have hR := f.addIdentity.abs_toFun_sub_approxAt_le n.interval.rightCode t
  have hL := f.addIdentity.abs_toFun_sub_approxAt_le n.interval.leftCode t
  rw [RatIntervalCode.value_rightCode] at hR
  have hval : ((RatCode.value (slopeCode f P n) : ℚ) : ℝ)
      = (((f.addIdentity.approxAt n.interval.rightCode t : ℚ) : ℝ)
          - ((f.addIdentity.approxAt n.interval.leftCode t : ℚ) : ℝ)) / n.interval.width := by
    simp only [slopeCode]
    rw [RatCode.value_divNNRat hwq, RatCode.value_sub]
    push_cast
    rfl
  have hne : n.interval.right - n.interval.left = n.interval.width := by
    rw [RatIntervalCode.right]
    ring
  rw [hval, slope_def_field, hne, ← sub_div, abs_div, abs_of_pos hw, div_le_iff₀ hw]
  have hbound : |((f.addIdentity.approxAt n.interval.rightCode t : ℚ) : ℝ)
      - ((f.addIdentity.approxAt n.interval.leftCode t : ℚ) : ℝ)
      - (f.addIdentity.toFun n.interval.right - f.addIdentity.toFun n.interval.left)|
      ≤ 2 * (2⁻¹ : ℝ) ^ t := by
    rw [abs_sub_comm] at hR
    calc _ = |(((f.addIdentity.approxAt n.interval.rightCode t : ℚ) : ℝ)
            - f.addIdentity.toFun n.interval.right)
          + (f.addIdentity.toFun n.interval.left
            - ((f.addIdentity.approxAt n.interval.leftCode t : ℚ) : ℝ))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (2⁻¹ : ℝ) ^ t + (2⁻¹ : ℝ) ^ t := add_le_add hR hL
      _ = 2 * (2⁻¹ : ℝ) ^ t := by ring
  refine le_trans hbound ?_
  rw [OscillationParams.margin]
  have : 0 ≤ (2⁻¹ : ℝ) ^ t := by positivity
  nlinarith

-- Only the sample's computability and error are used from here on.
attribute [local irreducible] slopeCode

/-- The resolved state on the current interval: betting switches to waiting exactly when the
sample exceeds `γ`, waiting switches to betting exactly when it is below `β`. -/
noncomputable def nextBetting (n : OscNode) : Bool :=
  bif n.betting then !(RatCode.lt (RatCode.ofNNRat P.gammaCode) (slopeCode f P n))
  else RatCode.lt (slopeCode f P n) (RatCode.ofNNRat P.betaCode)

theorem computable_nextBetting : Computable (nextBetting f P) := by
  have hs := computable_slopeCode f P
  have hup := RatCode.primrec_lt.to_comp.comp (Computable.const (RatCode.ofNNRat P.gammaCode)) hs
  have hdown := RatCode.primrec_lt.to_comp.comp hs (Computable.const (RatCode.ofNNRat P.betaCode))
  exact (Computable.cond primrec_betting.to_comp (Primrec.not.to_comp.comp hup) hdown).of_eq
    fun _ ↦ rfl

attribute [local irreducible] nextBetting

/-- Whether the resolved state `nb` differs from the node's state. -/
def switched (nb : Bool) (n : OscNode) : Bool := bif nb then !n.betting else n.betting

theorem switched_iff (nb : Bool) (n : OscNode) : switched nb n = true ↔ nb ≠ n.betting := by
  cases nb <;> cases hb : n.betting <;> simp [switched, hb]

/-- A regridding move must be taken exactly on a switch or at the root. -/
def needsRegrid (nb : Bool) (n : OscNode) : Bool := switched nb n || !n.cell.isSome

/-- The regridding child in grid `G` for the resolved state `nb`: it must pass the regridding test
with the half-width condition exactly on entering waiting, and the anchor is reset on a switch. -/
def regridStep (G : AffineDyadicGrid) (nb : Bool) (n : OscNode) (c : AffineDyadicCell) :
    Option OscNode :=
  bif needsRegrid nb n && regridChild n.interval G (!nb) c then
    some
      { interval := G.cellCode c
        values := n.values ++ [⟨nb, n.interval, G.cellCode c⟩]
        betting := nb
        cell := some c
        phaseStart := bif switched nb n then n.toOscFrame else n.phaseStart }
  else none

/-- The binary child, allowed only while the state is retained on an existing cell. -/
def binaryStep (nb : Bool) (n : OscNode) (b : Bool) : Option OscNode :=
  bif needsRegrid nb n then none
  else some
    { interval := n.interval.child b
      values := n.values ++ [⟨n.betting, n.interval, n.interval.child b⟩]
      betting := n.betting
      cell := n.cell.map fun c ↦ c.child b
      phaseStart := n.phaseStart }

theorem primrec_switched : Primrec₂ switched :=
  Primrec.cond Primrec.fst (Primrec.not.comp (primrec_betting.comp Primrec.snd))
    (primrec_betting.comp Primrec.snd)

theorem primrec_needsRegrid : Primrec₂ needsRegrid :=
  Primrec.or.comp primrec_switched
    (Primrec.not.comp (Primrec.option_isSome.comp (primrec_cell.comp Primrec.snd)))

theorem primrec_regridStep (G : AffineDyadicGrid) (nb : Bool) :
    Primrec₂ (regridStep G nb) := by
  have hn : Primrec fun q : OscNode × AffineDyadicCell ↦ q.1 := Primrec.fst
  have hc : Primrec fun q : OscNode × AffineDyadicCell ↦ q.2 := Primrec.snd
  have hI := primrec_interval.comp hn
  have hneed := primrec_needsRegrid.comp (Primrec.const nb) hn
  have htest := Primrec.and.comp hneed ((primrec_regridChild G (!nb)).comp hI hc)
  have hcell := G.primrec_cellCode.comp hc
  have hstep := OscInterpStep.primrec_mk.comp ((Primrec.const nb).pair (hI.pair hcell))
  have hvals := Primrec.list_concat.comp (primrec_values.comp hn) hstep
  have hframe := OscFrame.primrec_mk.comp (hcell.pair hvals)
  have hanchor := Primrec.cond (primrec_switched.comp (Primrec.const nb) hn)
    (primrec_toOscFrame.comp hn) (primrec_phaseStart.comp hn)
  have hnode := primrec_mk.comp
    (hframe.pair ((Primrec.const nb).pair ((Primrec.option_some.comp hc).pair hanchor)))
  exact (Primrec.cond htest (Primrec.option_some.comp hnode) (Primrec.const none)).of_eq
    fun _ ↦ rfl

theorem primrec_binaryStep (nb : Bool) : Primrec₂ (binaryStep nb) := by
  have hn : Primrec fun q : OscNode × Bool ↦ q.1 := Primrec.fst
  have hb : Primrec fun q : OscNode × Bool ↦ q.2 := Primrec.snd
  have hI := primrec_interval.comp hn
  have hIc := primrec_ratIntervalCode_child.comp hI hb
  have hbet := primrec_betting.comp hn
  have hstep := OscInterpStep.primrec_mk.comp (hbet.pair (hI.pair hIc))
  have hvals := Primrec.list_concat.comp (primrec_values.comp hn) hstep
  have hframe := OscFrame.primrec_mk.comp (hIc.pair hvals)
  have hcell : Primrec fun q : OscNode × Bool ↦ q.1.cell.map fun c ↦ c.child q.2 :=
    Primrec.option_map (g := fun (q : OscNode × Bool) (c : AffineDyadicCell) ↦ c.child q.2)
      (primrec_cell.comp hn) (primrec_affineDyadicCell_child.comp Primrec.snd (hb.comp Primrec.fst))
  have hnode := primrec_mk.comp
    (hframe.pair (hbet.pair (hcell.pair (primrec_phaseStart.comp hn))))
  exact (Primrec.cond (primrec_needsRegrid.comp (Primrec.const nb) hn) (Primrec.const none)
    (Primrec.option_some.comp hnode)).of_eq fun _ ↦ rfl

/-- One move from a node: resolve the state on the current interval once, then subdivide.
`Sum.inl b` is the binary child; `Sum.inr c` is a regridding child of the resolved state's grid. -/
noncomputable def step (n : OscNode) : Bool ⊕ AffineDyadicCell → Option OscNode
  | Sum.inl b => binaryStep (nextBetting f P n) n b
  | Sum.inr c =>
      bif nextBetting f P n then regridStep P.betGrid true n c else regridStep P.waitGrid false n c

theorem step_inl (n : OscNode) (b : Bool) :
    step f P n (Sum.inl b) = binaryStep (nextBetting f P n) n b := rfl

theorem step_inr (n : OscNode) (c : AffineDyadicCell) :
    step f P n (Sum.inr c) =
      bif nextBetting f P n then regridStep P.betGrid true n c
      else regridStep P.waitGrid false n c := rfl

theorem computable_step : Computable₂ (step f P) := by
  have hn : Computable fun q : OscNode × (Bool ⊕ AffineDyadicCell) ↦ q.1 := Computable.fst
  have hnb := (computable_nextBetting f P).comp hn
  have hbin : Computable₂ fun (q : OscNode × (Bool ⊕ AffineDyadicCell)) (b : Bool) ↦
      binaryStep (nextBetting f P q.1) q.1 b := by
    have hnb' := hnb.comp (Computable.fst (α := OscNode × (Bool ⊕ AffineDyadicCell)) (β := Bool))
    have hn' := hn.comp (Computable.fst (α := OscNode × (Bool ⊕ AffineDyadicCell)) (β := Bool))
    have hb : Computable fun r : (OscNode × (Bool ⊕ AffineDyadicCell)) × Bool ↦ r.2 :=
      Computable.snd
    exact (Computable.cond hnb' ((primrec_binaryStep true).to_comp.comp hn' hb)
      ((primrec_binaryStep false).to_comp.comp hn' hb)).of_eq fun r ↦ by
        cases h : nextBetting f P r.1.1 <;> simp [h]
  have hreg : Computable₂ fun (q : OscNode × (Bool ⊕ AffineDyadicCell)) (c : AffineDyadicCell) ↦
      bif nextBetting f P q.1 then regridStep P.betGrid true q.1 c
      else regridStep P.waitGrid false q.1 c := by
    have hnb' := hnb.comp
      (Computable.fst (α := OscNode × (Bool ⊕ AffineDyadicCell)) (β := AffineDyadicCell))
    have hn' := hn.comp
      (Computable.fst (α := OscNode × (Bool ⊕ AffineDyadicCell)) (β := AffineDyadicCell))
    have hc : Computable
        fun r : (OscNode × (Bool ⊕ AffineDyadicCell)) × AffineDyadicCell ↦ r.2 :=
      Computable.snd
    exact Computable.cond hnb' ((primrec_regridStep P.betGrid true).to_comp.comp hn' hc)
      ((primrec_regridStep P.waitGrid false).to_comp.comp hn' hc)
  exact (Computable.sumCasesOn Computable.snd hbin hreg).of_eq fun q ↦ by
    rcases q with ⟨n, b | c⟩ <;> rfl

/-- The node reached along a path of moves, if every move is allowed. -/
noncomputable def rawNode (path : List (Bool ⊕ AffineDyadicCell)) : Option OscNode :=
  path.foldl (fun o m ↦ o.bind fun n ↦ step f P n m) (some root)

@[simp] theorem rawNode_nil : rawNode f P [] = some root := rfl

theorem rawNode_append_singleton (path : List (Bool ⊕ AffineDyadicCell))
    (m : Bool ⊕ AffineDyadicCell) :
    rawNode f P (path ++ [m]) = (rawNode f P path).bind fun n ↦ step f P n m := by
  rw [rawNode, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem computable_rawNode : Computable (rawNode f P) := by
  have hstep : Computable₂ fun (_ : List (Bool ⊕ AffineDyadicCell))
      (r : Option OscNode × (Bool ⊕ AffineDyadicCell)) ↦ r.1.bind fun n ↦ step f P n r.2 :=
    Computable.option_bind (Computable.fst.comp Computable.snd)
      ((computable_step f P).comp Computable.snd (Computable.snd.comp (Computable.snd.comp
        Computable.fst)))
  exact (Computable.list_foldl Computable.id (Computable.const (some root)) hstep).of_eq
    fun _ ↦ rfl

end OscNode

end AlgorithmicRandomness
