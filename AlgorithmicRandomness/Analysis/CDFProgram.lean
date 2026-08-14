/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.Extension
import AlgorithmicRandomness.Martingale.Computable

/-!
# The dyadic program of a computable martingale

This closes the loop: a computable martingale with a bounded capital yields a
`ComputableLipschitz` whose function is the cumulative function of the martingale.

The coded prefix sum recurses on the *cut index*, not over a list. That is what makes fuel
unnecessary here, in contrast with `Simulate`, `Savings` and `Oscillation`. Those constructions
must run a program inside a program and therefore reason about how long it runs; here
`M.program.toFun` is already total and computable, so `Computable.nat_rec` composes it directly
and nothing needs to be said about termination.

It is worth being precise about what is *not* claimed. This is not a uniform syntactic transformer
taking an arbitrary raw `Code` to a grid code — the construction consumes a `ComputableMartingale`,
whose totality is part of the data. Uniformity was load-bearing for trimming and for the universal
test, where a program receives another program as input and must run it; no later universal machine
consumes the martingale code dynamically, and `ComputableLipschitz` asks only for one actual total
evaluation code, which `NatFunctionCode.ofComputable` supplies.

Out-of-range behaviour of the recursion is deliberately unconstrained: the correctness theorem is
bounded by `k ≤ 2 ^ n`, exactly as `ComputableLipschitz.eval_dyadic` is.
-/

open scoped NNReal NNRat

namespace AlgorithmicRandomness

/-! ## The level enumeration is primitive recursive -/

theorem primrec_levelWords : Primrec levelWords := by
  have hchildren : Primrec₂ fun (_ : ℕ × (ℕ × List BitString)) (σ : BitString) ↦
      [σ ++ [false], σ ++ [true]] :=
    Primrec.list_cons.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [false]))
      (Primrec.list_cons.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [true]))
        (Primrec.const []))
  have hstep : Primrec₂ fun (_ : ℕ) (p : ℕ × List BitString) ↦
      p.2.flatMap fun σ ↦ [σ ++ [false], σ ++ [true]] :=
    Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hchildren
  refine (Primrec.nat_rec' Primrec.id (Primrec.const [([] : BitString)]) hstep).of_eq fun n ↦ ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [levelWords_succ, ← ih]
    rfl

/-! ## The coded prefix sum -/

/-- The coded value of `gridCDF M n k`, by recursion on the cut index `k`. Each step adds the
`k`-th cell's contribution: its capital, divided by `2 ^ n`. -/
def gridCDFCode (M : ComputableMartingale) (n : ℕ) : ℕ → ℕ
  | 0 => NNRatCode.ofNat 0
  | k + 1 =>
      NNRatCode.add (gridCDFCode M n k)
        (NNRatCode.divPowTwo n
          (M.program.toFun (Encodable.encode ((levelWords n).getD k ([] : BitString)))))

/-- **Correctness**, in range. Each step is `gridCDF_succ` applied to the `k`-th cell, which
`gridIndex_getD_levelWords` identifies as the string of index `k`. -/
theorem value_gridCDFCode (M : ComputableMartingale) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    NNRatCode.value (gridCDFCode M n k) = gridCDF M.toTreeMartingale n k := by
  induction k with
  | zero => rw [gridCDFCode, NNRatCode.value_ofNat, gridCDF_zero]; norm_num
  | succ k ih =>
    have hklt : k < 2 ^ n := by omega
    have hklen : k < (levelWords n).length := by rw [length_levelWords]; exact hklt
    set σ := (levelWords n).getD k ([] : BitString) with hσ
    have hmem : σ ∈ levelWords n := by
      rw [hσ, List.getD_eq_getElem _ _ hklen]
      exact List.getElem_mem hklen
    have hlen : σ.length = n := length_of_mem_levelWords hmem
    have hidx : gridIndex σ = k := by rw [hσ]; exact gridIndex_getD_levelWords hklt
    rw [gridCDFCode, NNRatCode.value_add, ih (by omega), NNRatCode.value_divPowTwo,
      M.eval_capital σ]
    have hsucc := gridCDF_succ M.toTreeMartingale σ
    rw [hlen, hidx] at hsucc
    rw [hsucc]
    congr 1
    rw [div_eq_mul_inv, inv_pow, mul_comm]

theorem computable_gridCDFCode (M : ComputableMartingale) :
    Computable fun p : ℕ × ℕ ↦ gridCDFCode M p.1 p.2 := by
  have hcell : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      M.program.toFun (Encodable.encode ((levelWords r.1.1).getD r.2.1 ([] : BitString))) :=
    M.program.computable_toFun.comp
      (Primrec.encode.comp
        ((Primrec.list_getD ([] : BitString)).comp
          (primrec_levelWords.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))).to_comp
  have hstep : Computable₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ) ↦
      NNRatCode.add q.2 (NNRatCode.divPowTwo p.1
        (M.program.toFun (Encodable.encode ((levelWords p.1).getD q.1 ([] : BitString))))) :=
    NNRatCode.primrec_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (NNRatCode.primrec_divPowTwo.to_comp.comp (Computable.fst.comp Computable.fst) hcell)
  refine (Computable.nat_rec (f := fun p : ℕ × ℕ ↦ p.2)
    (g := fun _ : ℕ × ℕ ↦ NNRatCode.ofNat 0) Computable.snd (Computable.const _)
    hstep).of_eq fun p ↦ ?_
  obtain ⟨n, k⟩ := p
  induction k with
  | zero => rfl
  | succ k ih => rw [gridCDFCode, ← ih]

/-! ## Packaging

The signed representation is reached only at the boundary: the sum is computed in `NNRatCode`,
where the martingale's capital lives, and `RatCode.ofNNRat` widens it once, at the point where
`ComputableLipschitz` requires a possibly-signed value. -/

/-- The program of the bundle: level and index in, coded rational out. -/
def gridCDFProgram (M : ComputableMartingale) (m : ℕ) : ℕ :=
  RatCode.ofNNRat (gridCDFCode M m.unpair.1 m.unpair.2)

theorem computable_gridCDFProgram (M : ComputableMartingale) : Computable (gridCDFProgram M) :=
  RatCode.primrec_ofNNRat.to_comp.comp ((computable_gridCDFCode M).comp Primrec.unpair.to_comp)

/-- **The constructor.** A computable martingale with bounded capital is a computable Lipschitz
function, whose values at the dyadic points are its cumulative sums exactly. -/
noncomputable def ComputableMartingale.toComputableLipschitz (M : ComputableMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) : ComputableLipschitz where
  unitFun := unitCDF M.toTreeMartingale hK
  lipschitzBound := K
  lipschitz_unit := lipschitzWith_unitCDF M.toTreeMartingale hK
  dyadicCode := NatFunctionCode.ofComputable (computable_gridCDFProgram M)
  eval_dyadic n k hk := by
    rw [NatFunctionCode.apply₂, NatFunctionCode.ofComputable_toFun, gridCDFProgram,
      Nat.unpair_pair, RatCode.value_ofNNRat, value_gridCDFCode M hk, unitCDF_unitGridPoint]
    norm_cast

@[simp] theorem ComputableMartingale.toComputableLipschitz_lipschitzBound
    (M : ComputableMartingale) {K : ℕ} (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) :
    (M.toComputableLipschitz hK).lipschitzBound = K := rfl

/-- The packaged function is the cumulative function: it agrees with `dyadicCDF` at every dyadic
point, which by density pins it down on all of `[0, 1]`. -/
theorem toComputableLipschitz_toFun_gridPoint (M : ComputableMartingale) {K : ℕ}
    (hK : ∀ σ, M.capital σ ≤ (K : ℚ≥0)) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    (M.toComputableLipschitz hK).toFun (gridPoint n k)
      = dyadicCDF M.toTreeMartingale (UnitDyadic.ofGrid n k hk) := by
  rw [show gridPoint n k = ((unitGridPoint n k hk : Set.Icc (0 : ℝ) 1) : ℝ) from rfl,
    ComputableLipschitz.toFun_val, dyadicCDF_eq_gridCDF]
  exact unitCDF_unitGridPoint M.toTreeMartingale hK hk

end AlgorithmicRandomness
