/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.Lipschitz
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# Computable nondecreasing functions

The presentation BMN's differentiability theorem is stated against: a continuous nondecreasing
function on `[0, 1]` whose values are *computable reals*, uniformly in a rational argument.

Four decisions are worth recording.

*Values are computable reals, not exact rationals.* `ComputableLipschitz` carries exact rational
values at dyadic cut points; the auxiliary function BMN builds has no such presentation, so the
data here is an approximation program with a `2⁻ᵏ` guarantee.

*Arguments are arbitrary signed coded rationals.* The intervals downstream are rationally scaled
and shifted, so their endpoints are rational but not dyadic, and shifting can move them outside
`[0, 1]`. The contract is therefore unconditional in the argument: the approximated value is the
one at the *clamped* argument, which is exactly what the ambient extension returns there. No use
site has to carry a side condition.

*Continuity is a field; an effective modulus is not.* BMN's functions are continuous, and their
construction proves continuity as a substantive step before appealing to the fact that a
continuous nondecreasing function with computable values on a dense rational family is computable.
Dropping the field would give a weaker "computable on rationals" presentation and would no longer
formalize the standard statement. An *effective* modulus is a different matter: nothing downstream
consumes one, and requiring it would add a real obligation to the hardest construction.

*Executable API stays code-valued.* There is no usable `Primcodable ℚ` — that is why `RatCode`
exists — so `approxAtCode` is the computable object and `approxAt` is only its semantic value.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-- A continuous nondecreasing function on `[0, 1]` together with a program approximating its
values at rational arguments. -/
structure ComputableMonotone where
  /-- The function, on the interval where the data determines it. -/
  unitFun : Set.Icc (0 : ℝ) 1 → ℝ
  /-- Nondecreasing, which is what the slope arguments consume. -/
  monotone_unitFun : Monotone unitFun
  /-- Continuous, which the interval-tree construction has to prove. -/
  continuous_unitFun : Continuous unitFun
  /-- The program: on `Nat.pair q k`, a coded rational within `2⁻ᵏ` of the value at `q`. -/
  approxCode : NatFunctionCode
  /-- The correctness bridge, unconditional in the argument: outside `[0, 1]` it constrains the
  approximation to the clamped value, which is what the ambient extension returns. -/
  approx_spec : ∀ q k : ℕ,
    |unitExtend unitFun ((RatCode.value q : ℚ) : ℝ)
        - ((RatCode.value (approxCode.apply₂ q k) : ℚ) : ℝ)| ≤ (2⁻¹ : ℝ) ^ k

namespace ComputableMonotone

variable (g : ComputableMonotone)

/-- The ambient function on `ℝ`, constant outside `[0, 1]`. -/
noncomputable def toFun : ℝ → ℝ := unitExtend g.unitFun

@[simp] theorem toFun_val (x : Set.Icc (0 : ℝ) 1) : g.toFun (x : ℝ) = g.unitFun x :=
  unitExtend_val g.unitFun x

theorem toFun_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : g.toFun x = g.unitFun ⟨x, hx⟩ :=
  unitExtend_of_mem g.unitFun hx

theorem monotone_toFun : Monotone g.toFun := g.monotone_unitFun.IccExtend zero_le_one

theorem continuous_toFun : Continuous g.toFun :=
  g.continuous_unitFun.comp continuous_projIcc

/-! ## The approximation API

The code is the computable object; the rational is only its value. -/

/-- The coded approximation to the value at the rational coded by `q`, to within `2⁻ᵏ`. -/
def approxAtCode (q k : ℕ) : ℕ := g.approxCode.apply₂ q k

/-- Its semantic value. Not an executable object: there is no `Primcodable ℚ`. -/
noncomputable def approxAt (q k : ℕ) : ℚ := RatCode.value (g.approxAtCode q k)

theorem computable_approxAtCode : Computable₂ g.approxAtCode := g.approxCode.computable_apply₂

theorem abs_toFun_sub_approxAt_le (q k : ℕ) :
    |g.toFun ((RatCode.value q : ℚ) : ℝ) - ((g.approxAt q k : ℚ) : ℝ)| ≤ (2⁻¹ : ℝ) ^ k :=
  g.approx_spec q k

end ComputableMonotone

/-! ## Clamping agrees with the ambient projection

The one bridge both constructors need: the coded clamp of a signed rational is the projection of
its value into `[0, 1]`. -/

theorem coe_value_clampUnit (q : ℕ) :
    (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ)
      = (Set.projIcc (0 : ℝ) 1 zero_le_one ((RatCode.value q : ℚ) : ℝ) : ℝ) := by
  rw [Set.coe_projIcc, RatCode.value_clampUnit]
  push_cast
  rfl

theorem coe_value_clampUnit_mem (q : ℕ) :
    (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [coe_value_clampUnit]
  exact (Set.projIcc (0 : ℝ) 1 zero_le_one _).2

theorem unitExtend_value_eq (u : Set.Icc (0 : ℝ) 1 → ℝ) (q : ℕ) :
    unitExtend u ((RatCode.value q : ℚ) : ℝ)
      = u ⟨(((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ),
        coe_value_clampUnit_mem q⟩ := by
  rw [unitExtend, Set.IccExtend, Function.comp_apply]
  congr 1
  exact Subtype.ext (coe_value_clampUnit q).symm

/-! ## Extension from rational values

The supremum is taken over rational arguments *at or below* the point. The non-strict bound is
what makes the agreement at rational arguments exact, with no continuity hypothesis: the value at
`q` itself is in the family. Continuity of the result is then a separate obligation, discharged by
whatever construction supplies the values — it does not disappear from the representation. -/

/-- The nondecreasing extension of rational values to the unit interval. -/
noncomputable def supExtend (v : ℚ≥0 → ℝ) (x : Set.Icc (0 : ℝ) 1) : ℝ :=
  ⨆ q : {q : ℚ≥0 // ((q : ℚ) : ℝ) ≤ (x : ℝ)}, v (q : ℚ≥0)

variable {v : ℚ≥0 → ℝ}

/-- The index family is nonempty and bounded: both are needed by anyone reasoning about the
extension, so they are public. -/
theorem nonempty_supExtend_index (x : Set.Icc (0 : ℝ) 1) :
    Nonempty {q : ℚ≥0 // ((q : ℚ) : ℝ) ≤ (x : ℝ)} :=
  ⟨⟨0, by simpa using x.2.1⟩⟩

private theorem le_one_of_index (hv : Monotone v) {x : Set.Icc (0 : ℝ) 1}
    (q : {q : ℚ≥0 // ((q : ℚ) : ℝ) ≤ (x : ℝ)}) : v (q : ℚ≥0) ≤ v 1 := by
  refine hv ?_
  have h : ((q : ℚ≥0) : ℝ) ≤ 1 := le_trans q.2 x.2.2
  exact_mod_cast h

theorem bddAbove_supExtend_index (hv : Monotone v) (x : Set.Icc (0 : ℝ) 1) :
    BddAbove (Set.range fun q : {q : ℚ≥0 // ((q : ℚ) : ℝ) ≤ (x : ℝ)} ↦ v (q : ℚ≥0)) := by
  refine ⟨v 1, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact le_one_of_index hv q

theorem monotone_supExtend (hv : Monotone v) : Monotone (supExtend v) := by
  intro x y hxy
  haveI := nonempty_supExtend_index x
  refine ciSup_le fun q ↦ ?_
  haveI := nonempty_supExtend_index y
  exact le_ciSup_of_le (bddAbove_supExtend_index hv y) ⟨(q : ℚ≥0), le_trans q.2 hxy⟩ le_rfl

/-- Agreement at rational arguments, with no continuity hypothesis. -/
theorem supExtend_rat (hv : Monotone v) (q : ℚ≥0) (hq : ((q : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    supExtend v ⟨((q : ℚ) : ℝ), hq⟩ = v q := by
  haveI := nonempty_supExtend_index (⟨((q : ℚ) : ℝ), hq⟩ : Set.Icc (0 : ℝ) 1)
  refine le_antisymm (ciSup_le fun p ↦ hv ?_)
    (le_ciSup_of_le (bddAbove_supExtend_index hv _) ⟨q, le_rfl⟩ le_rfl)
  have h : ((p : ℚ≥0) : ℝ) ≤ ((q : ℚ≥0) : ℝ) := p.2
  exact_mod_cast h

/-- Package rational values as a bundle. The approximation contract is stated against the values
themselves, at the clamped argument; the extension bridge is discharged here rather than at every
construction site. -/
noncomputable def ofRationalValues (v : ℚ≥0 → ℝ) (hv : Monotone v)
    (hcont : Continuous (supExtend v)) (code : NatFunctionCode)
    (hcode : ∀ q k : ℕ, |v (NNRatCode.value (RatCode.clampUnit q))
        - ((RatCode.value (code.apply₂ q k) : ℚ) : ℝ)| ≤ (2⁻¹ : ℝ) ^ k) :
    ComputableMonotone where
  unitFun := supExtend v
  monotone_unitFun := monotone_supExtend hv
  continuous_unitFun := hcont
  approxCode := code
  approx_spec q k := by
    rw [unitExtend_value_eq, supExtend_rat hv]
    exact hcode q k

@[simp] theorem ofRationalValues_unitFun (v : ℚ≥0 → ℝ) (hv : Monotone v)
    (hcont : Continuous (supExtend v)) (code : NatFunctionCode) (hcode : _) :
    (ofRationalValues v hv hcont code hcode).unitFun = supExtend v := rfl

/-! ## Strictification

Adding the identity makes a nondecreasing function strictly increasing, with the quantitative form
`b - a ≤ F b - F a` that an interpolation proportional to the source needs as a denominator bound.
Differentiability is unaffected in the interior, since the two functions differ there by a linear
term. -/

namespace ComputableMonotone

variable (f : ComputableMonotone)

/-- The approximation program of `f + id`: the argument is exact, so only `f`'s error survives. -/
noncomputable def addIdentityFun (w : ℕ) : ℕ :=
  RatCode.add (f.approxAtCode w.unpair.1 w.unpair.2)
    (RatCode.ofNNRat (RatCode.clampUnit w.unpair.1))

theorem computable_addIdentityFun : Computable f.addIdentityFun := by
  have hq : Computable fun w : ℕ ↦ w.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
  have hk : Computable fun w : ℕ ↦ w.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
  have hf := Computable₂.comp f.computable_approxAtCode hq hk
  have hc := Computable₂.comp RatCode.primrec_add.to_comp hf
    ((RatCode.primrec_ofNNRat.comp
      (RatCode.primrec_clampUnit.comp (Primrec.fst.comp Primrec.unpair))).to_comp)
  exact hc.of_eq fun _ ↦ rfl

/-- **Strictification.** -/
noncomputable def addIdentity : ComputableMonotone where
  unitFun x := f.unitFun x + (x : ℝ)
  monotone_unitFun x y hxy := add_le_add (f.monotone_unitFun hxy) hxy
  continuous_unitFun := f.continuous_unitFun.add continuous_subtype_val
  approxCode := NatFunctionCode.ofComputable f.computable_addIdentityFun
  approx_spec q k := by
    rw [NatFunctionCode.apply₂, NatFunctionCode.ofComputable_toFun, addIdentityFun,
      Nat.unpair_pair, RatCode.value_add, Rat.cast_add, RatCode.value_ofNNRat,
      unitExtend_value_eq]
    have hbase := f.approx_spec q k
    rw [unitExtend_value_eq] at hbase
    simpa [approxAtCode] using hbase

@[simp] theorem addIdentity_unitFun (x : Set.Icc (0 : ℝ) 1) :
    f.addIdentity.unitFun x = f.unitFun x + (x : ℝ) := rfl

theorem strictMono_addIdentity : StrictMono f.addIdentity.unitFun := by
  intro x y hxy
  have hle : (x : ℝ) ≤ (y : ℝ) := le_of_lt hxy
  have hlt : (x : ℝ) < (y : ℝ) := hxy
  have := f.monotone_unitFun hle
  rw [addIdentity_unitFun, addIdentity_unitFun]
  linarith

theorem toFun_addIdentity {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    f.addIdentity.toFun x = f.toFun x + x := by
  rw [toFun_of_mem _ hx, toFun_of_mem _ hx, addIdentity_unitFun]

/-- The quantitative form the interpolation needs. -/
theorem sub_le_addIdentity_sub {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    b - a ≤ f.addIdentity.toFun b - f.addIdentity.toFun a := by
  rw [toFun_addIdentity _ ha, toFun_addIdentity _ hb]
  have := f.monotone_toFun hab
  linarith

theorem slope_addIdentity {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : a ≠ b) : slope f.addIdentity.toFun a b = slope f.toFun a b + 1 := by
  rw [slope_def_field, slope_def_field, toFun_addIdentity _ ha, toFun_addIdentity _ hb]
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp
  ring

theorem differentiableAt_addIdentity_iff {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ f.addIdentity.toFun z ↔ DifferentiableAt ℝ f.toFun z := by
  have hev : f.addIdentity.toFun =ᶠ[nhds z] fun x ↦ f.toFun x + x := by
    refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds hz.1 hz.2) fun x hx ↦ ?_
    exact toFun_addIdentity f (Set.Ioo_subset_Icc_self hx)
  rw [hev.differentiableAt_iff]
  constructor
  · intro h
    simpa using h.sub differentiable_id.differentiableAt
  · intro h
    exact h.add differentiable_id.differentiableAt

end ComputableMonotone

/-! ## Lipschitz functions become monotone ones

`f + K · x` is nondecreasing exactly because `K` bounds the slope. The approximation rounds the
clamped argument down to a dyadic cut point, where `f` has an exact value, and adds the linear term
exactly; the whole error is the Lipschitz error of that rounding. The rounding level is `k + K`,
which suffices because `K ≤ 2 ^ K` — so no coded logarithm is needed. -/

namespace ComputableLipschitz

variable (f : ComputableLipschitz)

/-- The rounding level for precision `k`. -/
def roundLevel (k : ℕ) : ℕ := k + f.lipschitzBound

/-- The index of the cut point at or below the clamped argument. -/
def roundIndex (q k : ℕ) : ℕ :=
  NNRatCode.floorScalePowTwo (f.roundLevel k) (RatCode.clampUnit q)

/-- The approximation program, on `Nat.pair q k`. -/
def monotoneApproxFun (input : ℕ) : ℕ :=
  RatCode.add (f.dyadicCode.apply₂ (f.roundLevel input.unpair.2)
      (f.roundIndex input.unpair.1 input.unpair.2))
    (RatCode.ofNNRat (NNRatCode.mul (NNRatCode.ofNat f.lipschitzBound)
      (RatCode.clampUnit input.unpair.1)))

theorem computable_monotoneApproxFun : Computable f.monotoneApproxFun := by
  have hclamp : Primrec fun input : ℕ ↦ RatCode.clampUnit input.unpair.1 :=
    RatCode.primrec_clampUnit.comp (Primrec.fst.comp Primrec.unpair)
  have hlevel : Primrec fun input : ℕ ↦ f.roundLevel input.unpair.2 :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const _)
  have hindex : Primrec fun input : ℕ ↦ f.roundIndex input.unpair.1 input.unpair.2 :=
    NNRatCode.primrec_floorScalePowTwo.comp hlevel hclamp
  have hpair : Computable fun input : ℕ ↦
      (f.roundLevel input.unpair.2, f.roundIndex input.unpair.1 input.unpair.2) :=
    Computable.pair hlevel.to_comp hindex.to_comp
  have hdyadic : Computable fun input : ℕ ↦
      f.dyadicCode.apply₂ (f.roundLevel input.unpair.2)
        (f.roundIndex input.unpair.1 input.unpair.2) :=
    (f.dyadicCode.computable_apply₂.comp Computable.fst Computable.snd).comp hpair
  have hlinear : Primrec fun input : ℕ ↦
      RatCode.ofNNRat (NNRatCode.mul (NNRatCode.ofNat f.lipschitzBound)
        (RatCode.clampUnit input.unpair.1)) :=
    RatCode.primrec_ofNNRat.comp
      (NNRatCode.primrec_mul.comp (Primrec.const _) hclamp)
  have hsum : Computable fun input : ℕ ↦
      (f.dyadicCode.apply₂ (f.roundLevel input.unpair.2)
          (f.roundIndex input.unpair.1 input.unpair.2),
        RatCode.ofNNRat (NNRatCode.mul (NNRatCode.ofNat f.lipschitzBound)
          (RatCode.clampUnit input.unpair.1))) :=
    Computable.pair hdyadic hlinear.to_comp
  exact ((RatCode.primrec_add.to_comp.comp Computable.fst Computable.snd).comp hsum).of_eq
    fun _ ↦ rfl

/-! ### The estimate

The linear terms cancel exactly, so the whole error is the Lipschitz error of the rounding. -/

theorem monotone_addLinear :
    Monotone fun x : Set.Icc (0 : ℝ) 1 ↦ f.unitFun x + f.lipschitzBound * (x : ℝ) := by
  intro x y hxy
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  have hd := f.dist_le (x : ℝ) (y : ℝ)
  rw [f.toFun_val, f.toFun_val] at hd
  have habs : |(x : ℝ) - (y : ℝ)| = (y : ℝ) - (x : ℝ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [habs] at hd
  have h1 : f.unitFun x - f.unitFun y ≤ (f.lipschitzBound : ℝ) * ((y : ℝ) - (x : ℝ)) :=
    le_trans (le_abs_self _) hd
  simp only []
  linarith

theorem continuous_addLinear :
    Continuous fun x : Set.Icc (0 : ℝ) 1 ↦ f.unitFun x + f.lipschitzBound * (x : ℝ) :=
  f.lipschitz_unit.continuous.add (continuous_const.mul continuous_subtype_val)

private theorem roundIndex_le (q k : ℕ) : f.roundIndex q k ≤ 2 ^ f.roundLevel k := by
  have hle := NNRatCode.floorScalePowTwo_le (f.roundLevel k) (RatCode.clampUnit q)
  have hone : NNRatCode.value (RatCode.clampUnit q) ≤ 1 := by
    have h := (RatCode.value_clampUnit q).le.trans (max_le (by norm_num) (min_le_left _ _))
    exact_mod_cast h
  have : ((f.roundIndex q k : ℕ) : ℚ≥0) ≤ 2 ^ f.roundLevel k := by
    refine le_trans hle ?_
    calc NNRatCode.value (RatCode.clampUnit q) * 2 ^ f.roundLevel k
        ≤ 1 * 2 ^ f.roundLevel k := by gcongr
      _ = 2 ^ f.roundLevel k := one_mul _
  exact_mod_cast this

private theorem abs_sub_gridPoint_le (q k : ℕ) :
    |(((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ)
        - gridPoint (f.roundLevel k) (f.roundIndex q k)| ≤ (2⁻¹ : ℝ) ^ f.roundLevel k := by
  have hpow : (0 : ℝ) < 2 ^ f.roundLevel k := by positivity
  have hle : ((f.roundIndex q k : ℕ) : ℝ)
      ≤ (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ) * 2 ^ f.roundLevel k := by
    exact_mod_cast NNRatCode.floorScalePowTwo_le (f.roundLevel k) (RatCode.clampUnit q)
  have hlt : (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ) * 2 ^ f.roundLevel k
      < ((f.roundIndex q k : ℕ) : ℝ) + 1 := by
    exact_mod_cast NNRatCode.lt_floorScalePowTwo_add_one (f.roundLevel k) (RatCode.clampUnit q)
  have hd1 : ((f.roundIndex q k : ℕ) : ℝ) / 2 ^ f.roundLevel k
      ≤ (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ) := (div_le_iff₀ hpow).mpr hle
  have hd2 : (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ)
      ≤ ((f.roundIndex q k : ℕ) : ℝ) / 2 ^ f.roundLevel k + 1 / 2 ^ f.roundLevel k := by
    have h := (le_div_iff₀ hpow).mpr hlt.le
    rw [add_div] at h
    exact h
  rw [gridPoint, inv_pow, ← one_div, abs_le]
  constructor <;> linarith

theorem monotoneApprox_spec (q k : ℕ) :
    |unitExtend (fun x : Set.Icc (0 : ℝ) 1 ↦ f.unitFun x + f.lipschitzBound * (x : ℝ))
        ((RatCode.value q : ℚ) : ℝ)
      - ((RatCode.value (f.monotoneApproxFun (Nat.pair q k)) : ℚ) : ℝ)| ≤ (2⁻¹ : ℝ) ^ k := by
  have hdy : ((RatCode.value (f.dyadicCode.apply₂ (f.roundLevel k) (f.roundIndex q k)) : ℚ) : ℝ)
      = f.toFun (gridPoint (f.roundLevel k) (f.roundIndex q k)) :=
    f.eval_dyadic_toFun (f.roundIndex_le q k)
  have hlin : ((RatCode.value (RatCode.ofNNRat (NNRatCode.mul
        (NNRatCode.ofNat f.lipschitzBound) (RatCode.clampUnit q))) : ℚ) : ℝ)
      = (f.lipschitzBound : ℝ) * (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ) := by
    rw [RatCode.value_ofNNRat, NNRatCode.value_mul, NNRatCode.value_ofNat]
    push_cast
    ring
  have hleft : unitExtend (fun x : Set.Icc (0 : ℝ) 1 ↦ f.unitFun x + f.lipschitzBound * (x : ℝ))
      ((RatCode.value q : ℚ) : ℝ)
      = f.toFun (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ)
        + (f.lipschitzBound : ℝ) * (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ) := by
    rw [unitExtend_value_eq, ← f.toFun_val ⟨_, coe_value_clampUnit_mem q⟩]
  have hright : ((RatCode.value (f.monotoneApproxFun (Nat.pair q k)) : ℚ) : ℝ)
      = f.toFun (gridPoint (f.roundLevel k) (f.roundIndex q k))
        + (f.lipschitzBound : ℝ) * (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ) := by
    rw [monotoneApproxFun, Nat.unpair_pair, RatCode.value_add, Rat.cast_add, hdy, hlin]
  have hKbound : (f.lipschitzBound : ℝ) * (2⁻¹ : ℝ) ^ f.lipschitzBound ≤ 1 := by
    rw [inv_pow, mul_comm, ← div_eq_inv_mul, div_le_one (by positivity)]
    exact_mod_cast Nat.lt_two_pow_self.le
  rw [hleft, hright, add_sub_add_right_eq_sub]
  calc |f.toFun (((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ)
          - f.toFun (gridPoint (f.roundLevel k) (f.roundIndex q k))|
      ≤ (f.lipschitzBound : ℝ)
          * |(((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) : ℝ)
            - gridPoint (f.roundLevel k) (f.roundIndex q k)| := f.dist_le _ _
    _ ≤ (f.lipschitzBound : ℝ) * (2⁻¹ : ℝ) ^ f.roundLevel k := by
        gcongr
        exact f.abs_sub_gridPoint_le q k
    _ = ((f.lipschitzBound : ℝ) * (2⁻¹ : ℝ) ^ f.lipschitzBound) * (2⁻¹ : ℝ) ^ k := by
        rw [roundLevel, pow_add]; ring
    _ ≤ 1 * (2⁻¹ : ℝ) ^ k := by gcongr
    _ = (2⁻¹ : ℝ) ^ k := one_mul _

/-- **Gate 1's bridge.** A computable Lipschitz function becomes a computable nondecreasing one by
adding `K · x`. -/
noncomputable def toComputableMonotone : ComputableMonotone where
  unitFun x := f.unitFun x + f.lipschitzBound * (x : ℝ)
  monotone_unitFun := f.monotone_addLinear
  continuous_unitFun := f.continuous_addLinear
  approxCode := NatFunctionCode.ofComputable f.computable_monotoneApproxFun
  approx_spec q k := by
    rw [NatFunctionCode.apply₂, NatFunctionCode.ofComputable_toFun]
    exact f.monotoneApprox_spec q k

@[simp] theorem toComputableMonotone_unitFun (x : Set.Icc (0 : ℝ) 1) :
    f.toComputableMonotone.unitFun x = f.unitFun x + f.lipschitzBound * (x : ℝ) := rfl

end ComputableLipschitz

end AlgorithmicRandomness
