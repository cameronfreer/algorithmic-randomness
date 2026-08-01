/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.PartrecCode

/-!
# Codes for total functions

A `NatFunctionCode` bundles a program, the total function it computes, and the evaluation
witness. Totality is *asserted data* carried alongside the code; nothing here claims that
totality is effectively certifiable, and the type is deliberately not enumerable.

Binary use goes through paired inputs (`apply₂`), not through a second, binary code hierarchy.

The constructor that matters downstream is `ofPartrecTotal`, which bundles a partial recursive
function that happens to be total: `toFun` is its `Part.get`, so no classical `Nat.find`
witness is involved and no explicit bound on `evaln` fuel is ever needed.
-/

open Nat.Partrec (Code)

namespace AlgorithmicRandomness

/-- A code together with the total function it computes and the evaluation witness. -/
structure NatFunctionCode where
  /-- The total function computed by the program. -/
  toFun : ℕ → ℕ
  /-- The underlying program. -/
  program : Code
  /-- The evaluation witness, which also asserts totality. -/
  eval_program : ∀ n, program.eval n = Part.some (toFun n)

namespace NatFunctionCode

/-- Bundle a partial recursive function that happens to be total, taking its values as
`Part.get`. This avoids both a classical choice of witness and any fuel estimate. -/
noncomputable def ofPartrecTotal {f : ℕ →. ℕ} (hf : Nat.Partrec f) (htot : ∀ n, (f n).Dom) :
    NatFunctionCode where
  toFun n := (f n).get (htot n)
  program := (Code.exists_code.mp hf).choose
  eval_program n := by
    rw [show (Code.exists_code.mp hf).choose.eval n = f n from
      congrFun (Code.exists_code.mp hf).choose_spec n]
    exact (Part.some_get _).symm

@[simp]
theorem ofPartrecTotal_toFun {f : ℕ →. ℕ} (hf : Nat.Partrec f) (htot : ∀ n, (f n).Dom) (n : ℕ) :
    (ofPartrecTotal hf htot).toFun n = (f n).get (htot n) := rfl

/-- Bundle a total computable function. -/
noncomputable def ofComputable {f : ℕ → ℕ} (hf : Computable f) : NatFunctionCode :=
  ofPartrecTotal (Partrec.nat_iff.mp hf) fun _ ↦ trivial

@[simp]
theorem ofComputable_toFun {f : ℕ → ℕ} (hf : Computable f) (n : ℕ) :
    (ofComputable hf).toFun n = f n := rfl

/-- Binary application through the pairing function. -/
def apply₂ (f : NatFunctionCode) (n k : ℕ) : ℕ := f.toFun (Nat.pair n k)

theorem eval_program_pair (f : NatFunctionCode) (n k : ℕ) :
    f.program.eval (Nat.pair n k) = Part.some (f.apply₂ n k) :=
  f.eval_program _

end NatFunctionCode

end AlgorithmicRandomness
