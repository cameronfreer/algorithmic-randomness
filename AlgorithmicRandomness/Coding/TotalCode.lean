/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.Partrec

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

/-- A bundled total program computes its bundled function; consumers should not have to
reconstruct this. -/
theorem computable_toFun (f : NatFunctionCode) : Computable f.toFun := by
  have h : Partrec fun n : ℕ ↦ f.program.eval n :=
    Code.eval_part.comp (Computable.const f.program) Computable.id
  exact h.of_eq fun n ↦ f.eval_program n

theorem computable_apply₂ (f : NatFunctionCode) : Computable₂ f.apply₂ :=
  (f.computable_toFun.comp Primrec₂.natPair.to_comp).of_eq fun _ ↦ rfl

end NatFunctionCode

/-- A converged bounded evaluation agrees with the total function the code computes. -/
theorem evalD_eq {E : NatFunctionCode} {s n : ℕ}
    (h : (Code.evaln s E.program n).isSome) : evalD E.program s n = E.toFun n := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
  have hmem : m ∈ E.program.eval n := Code.evaln_sound hm
  rw [E.eval_program n, Part.mem_some_iff] at hmem
  rw [evalD, hm, Option.getD_some, hmem]

/-! ## Fuel along a path

A fold down the tree that consults the source program at each prefix needs the fuel to resolve
exactly those prefixes — no sibling, and nothing beyond the target. `evaln` fuel demands grow
fast enough in the encoded input that requiring more would be a real execution cost. -/

/-- The fuel `s` resolves the program on every prefix of `σ`. -/
def NatFunctionCode.PathFuelOk (E : NatFunctionCode) (s : ℕ) (σ : BitString) : Prop :=
  ∀ τ, τ <+: σ → evalD E.program s (Encodable.encode τ) = E.toFun (Encodable.encode τ)


/-- The executable fuel test: check `[]`, then each extended prefix. -/
def pathFuelOkStep (p : Code) (s : ℕ) (q : BitString × Bool) (b : Bool) : BitString × Bool :=
  (q.1 ++ [b], q.2 && (Code.evaln s p (Encodable.encode (q.1 ++ [b]))).isSome)

def pathFuelOkPair (p : Code) (s : ℕ) (σ : BitString) : BitString × Bool :=
  σ.foldl (pathFuelOkStep p s) ([], (Code.evaln s p (Encodable.encode ([] : BitString))).isSome)

def pathFuelOk (p : Code) (s : ℕ) (σ : BitString) : Bool := (pathFuelOkPair p s σ).2

theorem foldl_pathFuelOkStep_fst (p : Code) (s : ℕ) (σ : BitString) :
    ∀ (τ : BitString) (v : Bool), (σ.foldl (pathFuelOkStep p s) (τ, v)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ v; simp
  | cons b σ ih => intro τ v; rw [List.foldl_cons, ih]; simp [pathFuelOkStep]

@[simp] theorem pathFuelOkPair_fst (p : Code) (s : ℕ) (σ : BitString) :
    (pathFuelOkPair p s σ).1 = σ := by
  rw [pathFuelOkPair, foldl_pathFuelOkStep_fst, List.nil_append]

@[simp] theorem pathFuelOk_nil (p : Code) (s : ℕ) :
    pathFuelOk p s [] = (Code.evaln s p (Encodable.encode ([] : BitString))).isSome := rfl

theorem pathFuelOk_append (p : Code) (s : ℕ) (σ : BitString) (b : Bool) :
    pathFuelOk p s (σ ++ [b])
      = (pathFuelOk p s σ && (Code.evaln s p (Encodable.encode (σ ++ [b]))).isSome) := by
  have h : pathFuelOkPair p s (σ ++ [b]) = pathFuelOkStep p s (pathFuelOkPair p s σ) b := by
    rw [pathFuelOkPair, pathFuelOkPair, List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold pathFuelOk
  rw [h, pathFuelOkStep, pathFuelOkPair_fst]

/-- The executable test certifies the semantic condition. -/
theorem pathFuelOk_spec {E : NatFunctionCode} {s : ℕ} {σ : BitString}
    (h : pathFuelOk E.program s σ = true) : E.PathFuelOk s σ := by
  induction σ using List.reverseRecOn with
  | nil =>
    intro τ hτ
    rw [List.prefix_nil.mp hτ]
    exact evalD_eq (by simpa using h)
  | append_singleton σ b ih =>
    rw [pathFuelOk_append, Bool.and_eq_true] at h
    intro τ hτ
    rcases (List.prefix_concat_iff).mp hτ with hcase | hcase
    · rw [hcase]; exact evalD_eq h.2
    · exact ih h.1 τ hcase

/-- Enough fuel always exists, because the source program is total. -/
theorem exists_pathFuelOk (E : NatFunctionCode) (σ : BitString) :
    ∃ s, pathFuelOk E.program s σ = true := by
  have hconv : ∀ n : ℕ, ∃ s, (Code.evaln s E.program n).isSome := by
    intro n
    obtain ⟨s, hs⟩ := Code.evaln_complete.mp (by rw [E.eval_program n]; exact Part.mem_some _)
    exact ⟨s, by rw [hs]; rfl⟩
  have hmono : ∀ {s t n : ℕ}, s ≤ t → (Code.evaln s E.program n).isSome →
      (Code.evaln t E.program n).isSome := by
    intro s t n hst h
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
    rw [Code.evaln_mono hst hm]; rfl
  have hokmono : ∀ {s t : ℕ} {τ : BitString}, s ≤ t → pathFuelOk E.program s τ = true →
      pathFuelOk E.program t τ = true := by
    intro s t τ hst
    induction τ using List.reverseRecOn with
    | nil => intro h; rw [pathFuelOk_nil] at h ⊢; exact hmono hst h
    | append_singleton τ c ihτ =>
      intro h
      rw [pathFuelOk_append, Bool.and_eq_true] at h ⊢
      exact ⟨ihτ h.1, hmono hst h.2⟩
  induction σ using List.reverseRecOn with
  | nil =>
    obtain ⟨s, hs⟩ := hconv (Encodable.encode ([] : BitString))
    exact ⟨s, by rw [pathFuelOk_nil, hs]⟩
  | append_singleton σ b ih =>
    obtain ⟨s₁, h₁⟩ := ih
    obtain ⟨s₂, h₂⟩ := hconv (Encodable.encode (σ ++ [b]))
    refine ⟨max s₁ s₂, ?_⟩
    rw [pathFuelOk_append, Bool.and_eq_true]
    exact ⟨hokmono (le_max_left _ _) h₁, hmono (le_max_right _ _) h₂⟩


theorem primrec_pathFuelOk :
    Primrec fun z : (Code × ℕ) × BitString ↦ pathFuelOk z.1.1 z.1.2 z.2 := by
  have hroot : Primrec fun z : (Code × ℕ) × BitString ↦
      (([], (Code.evaln z.1.2 z.1.1
        (Encodable.encode ([] : BitString))).isSome) : BitString × Bool) :=
    Primrec₂.pair.comp (Primrec.const [])
      (primrec_isSome.comp (Code.primrec_evaln.comp
        (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.const (Encodable.encode ([] : BitString))))))
  have hstep : Primrec₂ fun (z : (Code × ℕ) × BitString) (q : (BitString × Bool) × Bool) ↦
      pathFuelOkStep z.1.1 z.1.2 q.1 q.2 := by
    have hpref : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × Bool) × Bool) ↦
        v.2.1.1 ++ [v.2.2] :=
      Primrec.list_append.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    exact Primrec₂.pair.comp hpref
      (Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (primrec_isSome.comp (Code.primrec_evaln.comp
          (((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
            (Primrec.encode.comp hpref)))))
  exact Primrec.snd.comp (Primrec.list_foldl Primrec.snd hroot hstep)


end AlgorithmicRandomness
