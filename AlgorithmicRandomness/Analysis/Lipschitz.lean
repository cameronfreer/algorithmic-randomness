/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.DyadicGrid
import AlgorithmicRandomness.Coding.RatCode
import AlgorithmicRandomness.Coding.TotalCode

/-!
# Computable Lipschitz functions

The bundle carries three separable things: a semantic function, a Lipschitz estimate for it, and
a program producing its exact values at dyadic points. Keeping them separate is what lets the
computable content stay finite and rational while the function itself is an arbitrary real
function.

Three choices are worth recording, since each rules out a plausible alternative.

*The domain is `Icc 0 1`, not `ℝ`.* An arbitrary function on `ℝ` agreeing with computable data on
`[0, 1]` need not be computable anywhere outside, so a structure whose field is `ℝ → ℝ` would
either overclaim or force every user to carry a side condition. Here the honest object is the
restriction, and the ambient function is *derived*, canonically, by `Set.IccExtend` — the constant
extension off the interval. That extension is itself computable from the data, so nothing is
smuggled in.

*The Lipschitz bound is a natural number.* A general `ℝ≥0` bound would be no more expressive for
our purposes and would not be executable; a natural bound converts directly into a modulus of
continuity, which is what the effective statements need. Our own bound is `4`, so no generality
is lost.

*Values are `RatCode`, not `NNRatCode`.* The cumulative function of a martingale is nonnegative,
but "computable Lipschitz function" should not be a notion that silently means "nonnegative", so
the reusable definition permits signed values.
-/

open scoped NNReal NNRat

namespace AlgorithmicRandomness

/-- A Lipschitz function on `[0, 1]` together with a program computing its exact values at the
dyadic cut points. -/
structure ComputableLipschitz where
  /-- The function, on the interval where it is genuinely determined by the data. -/
  unitFun : Set.Icc (0 : ℝ) 1 → ℝ
  /-- A natural Lipschitz bound, so that it doubles as an executable modulus. -/
  lipschitzBound : ℕ
  /-- The estimate. -/
  lipschitz_unit : LipschitzWith (lipschitzBound : ℝ≥0) unitFun
  /-- The program, taking a level and an index to a coded rational. -/
  dyadicCode : NatFunctionCode
  /-- The correctness bridge, at every cut point of every level. -/
  eval_dyadic : ∀ (n k : ℕ) (hk : k ≤ 2 ^ n),
    ((RatCode.value (dyadicCode.apply₂ n k) : ℚ) : ℝ) = unitFun (unitGridPoint n k hk)

namespace ComputableLipschitz

/-- The ambient function on `ℝ`: constant outside `[0, 1]`. This is a canonical extension of the
data, not an arbitrary choice of one — which is what keeps the global statements honest. -/
noncomputable def toFun (f : ComputableLipschitz) : ℝ → ℝ :=
  Set.IccExtend zero_le_one f.unitFun

@[simp] theorem toFun_val (f : ComputableLipschitz) (x : Set.Icc (0 : ℝ) 1) :
    f.toFun (x : ℝ) = f.unitFun x :=
  Set.IccExtend_val zero_le_one f.unitFun x

theorem toFun_of_mem (f : ComputableLipschitz) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    f.toFun x = f.unitFun ⟨x, hx⟩ :=
  Set.IccExtend_of_mem zero_le_one f.unitFun hx

/-- The extension keeps the bound: `Set.projIcc` is `1`-Lipschitz, and `Set.IccExtend` is
literally the composite. -/
theorem lipschitzWith_toFun (f : ComputableLipschitz) :
    LipschitzWith (f.lipschitzBound : ℝ≥0) f.toFun := by
  have h := f.lipschitz_unit.comp (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1))
  rwa [mul_one] at h

theorem continuous_toFun (f : ComputableLipschitz) : Continuous f.toFun :=
  f.lipschitzWith_toFun.continuous

/-- The correctness bridge, transported to the ambient function. -/
theorem eval_dyadic_toFun (f : ComputableLipschitz) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    ((RatCode.value (f.dyadicCode.apply₂ n k) : ℚ) : ℝ) = f.toFun (gridPoint n k) := by
  rw [f.eval_dyadic n k hk, ← unitGridPoint_coe n k hk, toFun_val]

/-- The Lipschitz estimate in the form the chord arguments use. -/
theorem dist_le (f : ComputableLipschitz) (x y : ℝ) :
    |f.toFun x - f.toFun y| ≤ (f.lipschitzBound : ℝ) * |x - y| := by
  have h := f.lipschitzWith_toFun.dist_le_mul x y
  rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_natCast] at h

end ComputableLipschitz

end AlgorithmicRandomness
