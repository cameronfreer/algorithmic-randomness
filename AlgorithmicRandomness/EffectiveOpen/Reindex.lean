/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.EffectiveOpen.Code

/-!
# Reindexing coded families of open sets

Reindexing a uniformly c.e. family along a computable function is a *code* transformation:
`reindexCode c f` runs `c` at index `f n` when asked for index `n`, by rebuilding the paired
input. The exported theorems are semantic — `enumeratesString_reindexCode` and
`denote_reindex` — and the `Code.eval` shims stay private.

The totality of `f` enters as an ordinary hypothesis `∀ n, f.eval n = Part.some (g n)`, so no
bundled structure is needed here; callers supply their own witness. The concrete instance used
downstream is the fixed shift `e.shift m`, reindexing along the genuine code
`addConstCode m` for `n ↦ n + m`.
-/

open Nat.Partrec (Code)

namespace AlgorithmicRandomness

/-- Pointwise unfolding of `Code.eval` on a composition, definitionally. -/
private theorem eval_comp_apply (cf cg : Code) (n : ℕ) :
    (cf.comp cg).eval n = (cg.eval n).bind cf.eval := rfl

/-! ## Reindexing along a code -/

/-- Reindex a uniform family along `f`: on paired input `Nat.pair n k`, run `c` on
`Nat.pair (f n) k`. -/
def reindexCode (c f : Code) : Code :=
  c.comp (Code.pair (f.comp Code.left) Code.right)

theorem eval_reindexCode {c f : Code} {n m : ℕ} (hf : f.eval n = Part.some m) (k : ℕ) :
    (reindexCode c f).eval (Nat.pair n k) = c.eval (Nat.pair m k) := by
  rw [reindexCode, eval_comp_apply]
  have hx : (Code.pair (f.comp Code.left) Code.right).eval (Nat.pair n k)
      = Part.some (Nat.pair m k) := by
    simp [Code.eval, Seq.seq, Nat.unpair_pair, hf]
  rw [hx, Part.bind_some]

/-- Enumeration semantics of reindexing: the `n`-th set of `reindexCode c f` is the `f n`-th
set of `c`. -/
theorem enumeratesString_reindexCode {c f : Code} {n m : ℕ} {σ : BitString}
    (hf : f.eval n = Part.some m) :
    EnumeratesString (reindexCode c f) n σ ↔ EnumeratesString c m σ := by
  simp only [EnumeratesString, eval_reindexCode hf]

namespace UniformOpenCode

/-- Reindex the family denoted by `e` along the code `f`. -/
def reindex (e : UniformOpenCode) (f : Code) : UniformOpenCode :=
  ⟨reindexCode e.program f⟩

theorem denote_reindex {f : Code} {g : ℕ → ℕ} (hf : ∀ n, f.eval n = Part.some (g n))
    (e : UniformOpenCode) (n : ℕ) : (e.reindex f).denote n = e.denote (g n) := by
  ext x
  rw [mem_denote_iff_enumerates, mem_denote_iff_enumerates]
  exact exists_congr fun σ ↦ and_congr_left' (enumeratesString_reindexCode (hf n))

end UniformOpenCode

/-! ## Fixed shifts -/

/-- A code for `n ↦ n + m`: the `m`-fold composition of `succ`. -/
def addConstCode : ℕ → Code
  | 0 => Code.id
  | m + 1 => Code.comp Code.succ (addConstCode m)

theorem eval_addConstCode (m n : ℕ) : (addConstCode m).eval n = Part.some (n + m) := by
  induction m with
  | zero => simp [addConstCode, Code.eval_id]
  | succ m ih =>
    rw [addConstCode, eval_comp_apply, ih, Part.bind_some]
    simp [Code.eval, Nat.add_assoc]

namespace UniformOpenCode

/-- Shift the family by a fixed offset: `(e.shift m).denote n = e.denote (n + m)`. -/
def shift (e : UniformOpenCode) (m : ℕ) : UniformOpenCode :=
  e.reindex (addConstCode m)

theorem denote_shift (e : UniformOpenCode) (m n : ℕ) :
    (e.shift m).denote n = e.denote (n + m) :=
  denote_reindex (eval_addConstCode m) e n

end UniformOpenCode

end AlgorithmicRandomness
