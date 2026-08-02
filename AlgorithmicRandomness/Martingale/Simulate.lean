/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.Partrec
import AlgorithmicRandomness.Coding.RatCode
import AlgorithmicRandomness.Martingale.Computable

/-!
# Bounded-error rational simulation of an approximable martingale

A `ComputableMartingale` carries exact rational capital, but the martingales that arise from
measure-theoretic constructions are only computable *reals*. This file bridges the gap: from a
real-valued tree martingale together with a program computing rational approximations at a
computable rate, it builds an actual `ComputableMartingale` whose capital dominates the original
pointwise, so success transfers with nothing to prove.

## The construction

Walk down the tree with a left fold, carrying the current prefix and the current simulated
value. At a node the two children are set to `x + (a - b)/2` and `x + (b - a)/2`, where `a` and
`b` approximate the two child capitals to precision `σ.length + 1`. Fairness is then **exact by
construction** — `RatCode.value_childUpdate_add` — whatever the approximations happen to be.

## The invariant

Write `δ σ` for the difference between the simulated and the true capital. The update gives

  `δ (σ ++ [b]) - δ σ = ±(e₀ - e₁)/2`,

so each step moves `δ` by at most `2⁻⁽ˡᵉⁿ ⁺ ¹⁾` and the total variation along any path is at
most `1`. Initializing at the root with `approx [] 0 + 2` puts `δ []` in `[1, 3]`, hence

  `0 ≤ δ σ ≤ 4` for every `σ`.

The lower bound gives both nonnegativity of the simulated capital and pointwise domination of
the original; the upper bound is `simulate_le_add_four`. A single initialization does both jobs.
-/

open scoped NNRat NNReal

namespace AlgorithmicRandomness

/-- A real-valued tree martingale. Finiteness is built into `ℝ≥0`, which is what makes rational
approximation and the signed arithmetic of the simulation possible. -/
structure RealTreeMartingale where
  /-- The capital held after betting along `σ`. -/
  capital : BitString → ℝ≥0
  /-- Fairness: the two children average to the parent. -/
  fair : ∀ σ, capital (σ ++ [false]) + capital (σ ++ [true]) = 2 * capital σ

/-- A real-valued tree martingale together with a program computing rational approximations to
its capital at a computable rate. `NatFunctionCode` supplies both the function and its
evaluation witness, so no separate approximation field is needed. -/
structure ApproximableTreeMartingale extends RealTreeMartingale where
  /-- On input `⟨encode σ, i⟩`, a coded rational within `2⁻ⁱ` of `capital σ`. -/
  approxCode : NatFunctionCode
  /-- The approximation guarantee. -/
  approx_spec : ∀ σ i,
    |((NNRatCode.value (approxCode.apply₂ (Encodable.encode σ) i) : ℚ≥0) : ℝ)
      - (capital σ : ℝ)| ≤ (2 : ℝ)⁻¹ ^ i

namespace ApproximableTreeMartingale

variable (D : ApproximableTreeMartingale)

/-- The rational approximation to `capital σ` at precision `i`. -/
def approx (σ : BitString) (i : ℕ) : ℚ≥0 :=
  NNRatCode.value (D.approxCode.apply₂ (Encodable.encode σ) i)

theorem abs_approx_sub (σ : BitString) (i : ℕ) :
    |((D.approx σ i : ℚ≥0) : ℝ) - (D.capital σ : ℝ)| ≤ (2 : ℝ)⁻¹ ^ i := D.approx_spec σ i

end ApproximableTreeMartingale

/-! ## The left fold -/

/-- The root value: the crudest approximation, shifted up by `2`. The shift is what places `δ []`
in `[1, 3]` and hence keeps `δ` nonnegative all the way down. -/
def simRoot (E : NatFunctionCode) : ℕ :=
  RatCode.add (RatCode.ofNNRat (E.apply₂ (Encodable.encode ([] : BitString)) 0)) (RatCode.ofNat 2)

/-- One step of the walk: extend the prefix and update the value by the child rule. -/
def simStep (E : NatFunctionCode) (q : BitString × ℕ) (b : Bool) : BitString × ℕ :=
  (q.1 ++ [b],
    RatCode.childUpdate q.2
      (E.apply₂ (Encodable.encode (q.1 ++ [false])) (q.1.length + 1))
      (E.apply₂ (Encodable.encode (q.1 ++ [true])) (q.1.length + 1)) b)

/-- Walk from the root to `σ`, carrying the prefix and the simulated value. -/
def simPair (E : NatFunctionCode) (σ : BitString) : BitString × ℕ :=
  σ.foldl (simStep E) ([], simRoot E)

def simCode (E : NatFunctionCode) (σ : BitString) : ℕ := (simPair E σ).2

def simValue (E : NatFunctionCode) (σ : BitString) : ℚ := RatCode.value (simCode E σ)

theorem foldl_simStep_fst (E : NatFunctionCode) (σ : BitString) :
    ∀ (τ : BitString) (x : ℕ), (σ.foldl (simStep E) (τ, x)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ x; simp
  | cons b σ ih =>
    intro τ x
    rw [List.foldl_cons, ih]
    simp [simStep]

/-- The fold really does carry the prefix it has walked. -/
@[simp] theorem simPair_fst (E : NatFunctionCode) (σ : BitString) : (simPair E σ).1 = σ := by
  rw [simPair, foldl_simStep_fst, List.nil_append]

theorem simPair_append (E : NatFunctionCode) (σ : BitString) (b : Bool) :
    simPair E (σ ++ [b]) = simStep E (simPair E σ) b := by
  rw [simPair, simPair, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem simCode_nil (E : NatFunctionCode) : simCode E [] = simRoot E := by
  rw [simCode, simPair, List.foldl_nil]

/-- The exact child equation, which is what `List.foldl_append` buys us. -/
theorem simCode_append (E : NatFunctionCode) (σ : BitString) (b : Bool) :
    simCode E (σ ++ [b]) = RatCode.childUpdate (simCode E σ)
      (E.apply₂ (Encodable.encode (σ ++ [false])) (σ.length + 1))
      (E.apply₂ (Encodable.encode (σ ++ [true])) (σ.length + 1)) b := by
  rw [simCode, simPair_append, simStep, simPair_fst, simCode]

/-- **Exact fairness**, inherited from the child update and independent of approximation
quality. -/
theorem simValue_fair (E : NatFunctionCode) (σ : BitString) :
    simValue E (σ ++ [false]) + simValue E (σ ++ [true]) = 2 * simValue E σ := by
  rw [simValue, simValue, simValue, simCode_append, simCode_append]
  exact RatCode.value_childUpdate_add _ _ _

/-! ## The invariant -/

namespace ApproximableTreeMartingale

variable (D : ApproximableTreeMartingale)

/-- The deviation of the simulated value from the true capital. -/
def delta (σ : BitString) : ℝ := ((simValue D.approxCode σ : ℚ) : ℝ) - (D.capital σ : ℝ)

theorem simValue_eq (σ : BitString) :
    ((simValue D.approxCode σ : ℚ) : ℝ) = D.delta σ + (D.capital σ : ℝ) := by
  rw [delta]; ring

variable {D}

theorem delta_nil_mem : 1 ≤ D.delta [] ∧ D.delta [] ≤ 3 := by
  have h := D.abs_approx_sub [] 0
  rw [pow_zero] at h
  have hdelta : D.delta [] = ((D.approx [] 0 : ℚ≥0) : ℝ) - (D.capital [] : ℝ) + 2 := by
    rw [delta, simValue, simCode_nil, simRoot, RatCode.value_add, RatCode.value_ofNNRat,
      RatCode.value_ofNat, approx]
    push_cast
    ring
  rw [hdelta]
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- The exact one-step change in the deviation, on the `false` child. -/
theorem delta_append_false (σ : BitString) :
    D.delta (σ ++ [false]) - D.delta σ
      = ((((D.approx (σ ++ [false]) (σ.length + 1) : ℚ≥0) : ℝ)
            - (D.capital (σ ++ [false]) : ℝ))
          - (((D.approx (σ ++ [true]) (σ.length + 1) : ℚ≥0) : ℝ)
            - (D.capital (σ ++ [true]) : ℝ))) / 2 := by
  have hfairR : (D.capital (σ ++ [false]) : ℝ) + (D.capital (σ ++ [true]) : ℝ)
      = 2 * (D.capital σ : ℝ) := by exact_mod_cast D.fair σ
  rw [delta, delta, simValue, simValue, simCode_append, RatCode.value_childUpdate_false,
    ← simValue, ← approx, ← approx]
  push_cast
  linarith [hfairR]

/-- The exact one-step change in the deviation, on the `true` child. -/
theorem delta_append_true (σ : BitString) :
    D.delta (σ ++ [true]) - D.delta σ
      = ((((D.approx (σ ++ [true]) (σ.length + 1) : ℚ≥0) : ℝ)
            - (D.capital (σ ++ [true]) : ℝ))
          - (((D.approx (σ ++ [false]) (σ.length + 1) : ℚ≥0) : ℝ)
            - (D.capital (σ ++ [false]) : ℝ))) / 2 := by
  have hfairR : (D.capital (σ ++ [false]) : ℝ) + (D.capital (σ ++ [true]) : ℝ)
      = 2 * (D.capital σ : ℝ) := by exact_mod_cast D.fair σ
  rw [delta, delta, simValue, simValue, simCode_append, RatCode.value_childUpdate_true,
    ← simValue, ← approx, ← approx]
  push_cast
  linarith [hfairR]

/-- Each step moves the deviation by at most the current precision. -/
theorem abs_delta_append_sub (σ : BitString) (b : Bool) :
    |D.delta (σ ++ [b]) - D.delta σ| ≤ (2 : ℝ)⁻¹ ^ (σ.length + 1) := by
  have h0 := D.abs_approx_sub (σ ++ [false]) (σ.length + 1)
  have h1 := D.abs_approx_sub (σ ++ [true]) (σ.length + 1)
  rw [abs_le] at h0 h1
  cases b
  · rw [delta_append_false, abs_le]
    constructor
    · rw [le_div_iff₀ two_pos]; linarith [h0.1, h1.2]
    · rw [div_le_iff₀ two_pos]; linarith [h0.2, h1.1]
  · rw [delta_append_true, abs_le]
    constructor
    · rw [le_div_iff₀ two_pos]; linarith [h1.1, h0.2]
    · rw [div_le_iff₀ two_pos]; linarith [h1.2, h0.1]

/-- The total variation of the deviation along a path is at most `1`. -/
theorem abs_delta_sub_nil (σ : BitString) :
    |D.delta σ - D.delta []| ≤ 1 - (2 : ℝ)⁻¹ ^ σ.length := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b ih =>
    have hstep := abs_delta_append_sub (D := D) σ b
    have htri : |D.delta (σ ++ [b]) - D.delta []|
        ≤ |D.delta (σ ++ [b]) - D.delta σ| + |D.delta σ - D.delta []| :=
      abs_sub_le _ _ _
    have hlen : (σ ++ [b]).length = σ.length + 1 := by simp
    rw [hlen]
    have hhalf : (2 : ℝ)⁻¹ ^ (σ.length + 1) + (1 - (2 : ℝ)⁻¹ ^ σ.length)
        = 1 - (2 : ℝ)⁻¹ ^ (σ.length + 1) := by
      rw [pow_succ]
      ring
    calc |D.delta (σ ++ [b]) - D.delta []|
        ≤ |D.delta (σ ++ [b]) - D.delta σ| + |D.delta σ - D.delta []| := htri
      _ ≤ (2 : ℝ)⁻¹ ^ (σ.length + 1) + (1 - (2 : ℝ)⁻¹ ^ σ.length) := add_le_add hstep ih
      _ = 1 - (2 : ℝ)⁻¹ ^ (σ.length + 1) := hhalf

theorem delta_nonneg (σ : BitString) : 0 ≤ D.delta σ := by
  have h := abs_delta_sub_nil (D := D) σ
  have hroot := delta_nil_mem (D := D)
  have hpow : (0 : ℝ) < (2 : ℝ)⁻¹ ^ σ.length := by positivity
  rw [abs_le] at h
  linarith [h.1, hroot.1]

theorem delta_le_four (σ : BitString) : D.delta σ ≤ 4 := by
  have h := abs_delta_sub_nil (D := D) σ
  have hroot := delta_nil_mem (D := D)
  have hpow : (0 : ℝ) < (2 : ℝ)⁻¹ ^ σ.length := by positivity
  rw [abs_le] at h
  linarith [h.2, hroot.2]

theorem simValue_nonneg (σ : BitString) : 0 ≤ simValue D.approxCode σ := by
  have h : (0 : ℝ) ≤ ((simValue D.approxCode σ : ℚ) : ℝ) := by
    rw [simValue_eq]
    have := delta_nonneg (D := D) σ
    positivity
  exact_mod_cast h

end ApproximableTreeMartingale

/-! ## The executable simulator

Fuel-bounded first, then one `rfind`. The accumulator is a bare `BitString × ℕ` rather than an
`Option`: a call that has not yet converged contributes a default, and a separate `Bool`-valued
fold records whether every call along the path has converged. Keeping the `Option` out of the
accumulator matters for elaboration, since the fold's `Primcodable` instance is otherwise deeply
nested. -/

open Nat.Partrec (Code)

-- Proof-engineering boundary, not a public commitment: the coded-arithmetic operations unfold
-- into `Nat.unpair`, hence into `Nat.sqrt`, and elaboration explodes if `Primrec` composition
-- is allowed to whnf through them. Their semantic lemmas are already proved above, so nothing
-- in this section needs to see through the definitions.
attribute [local irreducible] RatCode.childUpdate RatCode.add RatCode.ofNNRat RatCode.ofNat

/-- Bounded evaluation with a default, so the value fold never carries an `Option`. -/
def evalD (p : Code) (s n : ℕ) : ℕ := (Code.evaln s p n).getD 0

private theorem primrec_evalD : Primrec fun z : (Code × ℕ) × ℕ ↦ evalD z.1.1 z.1.2 z.2 :=
  Primrec.option_getD.comp
    (Code.primrec_evaln.comp
      (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair Primrec.snd))
    (Primrec.const 0)

/-- The fuel-bounded analogue of `simRoot`. -/
def simRootAt (p : Code) (s : ℕ) : BitString × ℕ :=
  ([], RatCode.add (RatCode.ofNNRat (evalD p s (Nat.pair (Encodable.encode ([] : BitString)) 0)))
    (RatCode.ofNat 2))

/-- The fuel-bounded analogue of `simStep`. -/
def simStepAt (p : Code) (s : ℕ) (q : BitString × ℕ) (b : Bool) : BitString × ℕ :=
  (q.1 ++ [b],
    RatCode.childUpdate q.2
      (evalD p s (Nat.pair (Encodable.encode (q.1 ++ [false])) (q.1.length + 1)))
      (evalD p s (Nat.pair (Encodable.encode (q.1 ++ [true])) (q.1.length + 1))) b)

def simAt (p : Code) (s : ℕ) (σ : BitString) : BitString × ℕ :=
  σ.foldl (simStepAt p s) (simRootAt p s)

theorem simAt_append (p : Code) (s : ℕ) (σ : BitString) (b : Bool) :
    simAt p s (σ ++ [b]) = simStepAt p s (simAt p s σ) b := by
  rw [simAt, simAt, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Convergence of every evaluation the walk needs, folded along the same path as the value so
that the two share their append equation. -/
def simOkStep (p : Code) (s : ℕ) (q : BitString × Bool) (b : Bool) : BitString × Bool :=
  (q.1 ++ [b],
    q.2 && (Code.evaln s p
        (Nat.pair (Encodable.encode (q.1 ++ [false])) (q.1.length + 1))).isSome
      && (Code.evaln s p (Nat.pair (Encodable.encode (q.1 ++ [true])) (q.1.length + 1))).isSome)

def simOkPair (p : Code) (s : ℕ) (σ : BitString) : BitString × Bool :=
  σ.foldl (simOkStep p s)
    ([], (Code.evaln s p (Nat.pair (Encodable.encode ([] : BitString)) 0)).isSome)

def simOk (p : Code) (s : ℕ) (σ : BitString) : Bool := (simOkPair p s σ).2

theorem foldl_simOkStep_fst (p : Code) (s : ℕ) (σ : BitString) :
    ∀ (τ : BitString) (x : Bool), (σ.foldl (simOkStep p s) (τ, x)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ x; simp
  | cons b σ ih => intro τ x; rw [List.foldl_cons, ih]; simp [simOkStep]

@[simp] theorem simOkPair_fst (p : Code) (s : ℕ) (σ : BitString) : (simOkPair p s σ).1 = σ := by
  rw [simOkPair, foldl_simOkStep_fst, List.nil_append]

theorem simOk_append (p : Code) (s : ℕ) (σ : BitString) (b : Bool) :
    simOk p s (σ ++ [b]) = (simOk p s σ
      && (Code.evaln s p (Nat.pair (Encodable.encode (σ ++ [false])) (σ.length + 1))).isSome
      && (Code.evaln s p (Nat.pair (Encodable.encode (σ ++ [true])) (σ.length + 1))).isSome) := by
  rw [simOk, simOkPair, List.foldl_append, List.foldl_cons, List.foldl_nil, ← simOkPair,
    simOkStep, simOkPair_fst, simOk]

@[simp] theorem simOk_nil (p : Code) (s : ℕ) :
    simOk p s [] = (Code.evaln s p (Nat.pair (Encodable.encode ([] : BitString)) 0)).isSome := by
  rw [simOk, simOkPair, List.foldl_nil]

/-- The step on a flat tuple, so its computability proof never sees nested projections. -/
private def stepFlat (v : ((Code × ℕ) × (BitString × ℕ)) × Bool) : BitString × ℕ :=
  simStepAt v.1.1.1 v.1.1.2 v.1.2 v.2

private theorem primrec_stepFlat : Primrec stepFlat := by
  have hcode : Primrec fun v : ((Code × ℕ) × (BitString × ℕ)) × Bool ↦ v.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hfuel : Primrec fun v : ((Code × ℕ) × (BitString × ℕ)) × Bool ↦ v.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hpref : Primrec fun v : ((Code × ℕ) × (BitString × ℕ)) × Bool ↦ v.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hval : Primrec fun v : ((Code × ℕ) × (BitString × ℕ)) × Bool ↦ v.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hlen : Primrec fun v : ((Code × ℕ) × (BitString × ℕ)) × Bool ↦ v.1.2.1.length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp hpref)
  have hev : ∀ b : Bool, Primrec fun v : ((Code × ℕ) × (BitString × ℕ)) × Bool ↦
      evalD v.1.1.1 v.1.1.2 (Nat.pair (Encodable.encode (v.1.2.1 ++ [b])) (v.1.2.1.length + 1)) :=
    fun b ↦ primrec_evalD.comp ((hcode.pair hfuel).pair
      (Primrec₂.natPair.comp
        (Primrec.encode.comp (Primrec.list_append.comp hpref (Primrec.const [b]))) hlen))
  exact Primrec₂.pair.comp
    (Primrec.list_append.comp hpref (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
    (RatCode.primrec_childUpdate.comp
      ((hval.pair ((hev false).pair (hev true))).pair Primrec.snd))

theorem primrec_simAt : Primrec fun z : (Code × ℕ) × BitString ↦ simAt z.1.1 z.1.2 z.2 := by
  have hroot : Primrec fun z : (Code × ℕ) × BitString ↦ simRootAt z.1.1 z.1.2 :=
    Primrec₂.pair.comp (Primrec.const [])
      (RatCode.primrec_add.comp
        (RatCode.primrec_ofNNRat.comp
          (primrec_evalD.comp (Primrec.fst.pair
            (Primrec.const (Nat.pair (Encodable.encode ([] : BitString)) 0)))))
        (Primrec.const (RatCode.ofNat 2)))
  have hstep : Primrec₂ fun (z : (Code × ℕ) × BitString) (q : (BitString × ℕ) × Bool) ↦
      simStepAt z.1.1 z.1.2 q.1 q.2 :=
    primrec_stepFlat.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldl Primrec.snd hroot hstep

/-! ## Correctness of the fuel-bounded simulator -/

/-- A converged bounded evaluation agrees with the total function the code computes. -/
theorem evalD_eq {E : NatFunctionCode} {s n : ℕ}
    (h : (Code.evaln s E.program n).isSome) : evalD E.program s n = E.toFun n := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
  have hmem : m ∈ E.program.eval n := Code.evaln_sound hm
  rw [E.eval_program n, Part.mem_some_iff] at hmem
  rw [evalD, hm, Option.getD_some, hmem]

/-- Once every needed evaluation has converged, the bounded simulator computes the intended
value. -/
theorem simAt_eq (E : NatFunctionCode) {s : ℕ} :
    ∀ {σ : BitString}, simOk E.program s σ = true → simAt E.program s σ = simPair E σ := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil =>
    intro h
    rw [simOk_nil] at h
    rw [simAt, List.foldl_nil, simRootAt, evalD_eq h, simPair, List.foldl_nil, simRoot,
      NatFunctionCode.apply₂]
  | append_singleton σ b ih =>
    intro h
    rw [simOk_append, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hσ, hf⟩, ht⟩ := h
    rw [simAt_append, ih hσ, simStepAt, simPair_append, simStep, simPair_fst,
      evalD_eq hf, evalD_eq ht, NatFunctionCode.apply₂, NatFunctionCode.apply₂]

/-- Enough fuel always exists, because the approximation program is total. -/
theorem exists_simOk (E : NatFunctionCode) (σ : BitString) :
    ∃ s, simOk E.program s σ = true := by
  have hconv : ∀ n : ℕ, ∃ s, (Code.evaln s E.program n).isSome := by
    intro n
    obtain ⟨s, hs⟩ := Code.evaln_complete.mp
      (by rw [E.eval_program n]; exact Part.mem_some _)
    exact ⟨s, by rw [hs]; rfl⟩
  have hmono : ∀ {s t n : ℕ}, s ≤ t → (Code.evaln s E.program n).isSome →
      (Code.evaln t E.program n).isSome := by
    intro s t n hst h
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
    rw [Code.evaln_mono hst hm]; rfl
  induction σ using List.reverseRecOn with
  | nil =>
    obtain ⟨s, hs⟩ := hconv (Nat.pair (Encodable.encode ([] : BitString)) 0)
    exact ⟨s, by rw [simOk_nil, hs]⟩
  | append_singleton σ b ih =>
    obtain ⟨s₁, h₁⟩ := ih
    obtain ⟨s₂, h₂⟩ := hconv (Nat.pair (Encodable.encode (σ ++ [false])) (σ.length + 1))
    obtain ⟨s₃, h₃⟩ := hconv (Nat.pair (Encodable.encode (σ ++ [true])) (σ.length + 1))
    -- monotonicity of the whole fold, from monotonicity of each call
    have hokmono : ∀ {s t : ℕ} {τ : BitString}, s ≤ t → simOk E.program s τ = true →
        simOk E.program t τ = true := by
      intro s t τ hst
      induction τ using List.reverseRecOn with
      | nil => intro h; rw [simOk_nil] at h ⊢; exact hmono hst h
      | append_singleton τ c ihτ =>
        intro h
        rw [simOk_append, Bool.and_eq_true, Bool.and_eq_true] at h ⊢
        exact ⟨⟨ihτ h.1.1, hmono hst h.1.2⟩, hmono hst h.2⟩
    refine ⟨max s₁ (max s₂ s₃), ?_⟩
    rw [simOk_append, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hokmono (le_max_left _ _) h₁,
      hmono ((le_max_left s₂ s₃).trans (le_max_right _ _)) h₂⟩,
      hmono ((le_max_right s₂ s₃).trans (le_max_right _ _)) h₃⟩

/-! ## The simulator as a program

`RatCode.toNNRat` is applied unconditionally: its *totality* needs no sign proof, and only its
*correctness* for a particular martingale uses `delta_nonneg`. -/

private theorem primrec_okStepFlat :
    Primrec fun v : ((Code × ℕ) × (BitString × Bool)) × Bool ↦
      simOkStep v.1.1.1 v.1.1.2 v.1.2 v.2 := by
  have hcode : Primrec fun v : ((Code × ℕ) × (BitString × Bool)) × Bool ↦ v.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hfuel : Primrec fun v : ((Code × ℕ) × (BitString × Bool)) × Bool ↦ v.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hpref : Primrec fun v : ((Code × ℕ) × (BitString × Bool)) × Bool ↦ v.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hflag : Primrec fun v : ((Code × ℕ) × (BitString × Bool)) × Bool ↦ v.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hlen : Primrec fun v : ((Code × ℕ) × (BitString × Bool)) × Bool ↦ v.1.2.1.length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp hpref)
  have hev : ∀ b : Bool, Primrec fun v : ((Code × ℕ) × (BitString × Bool)) × Bool ↦
      (Code.evaln v.1.1.2 v.1.1.1
        (Nat.pair (Encodable.encode (v.1.2.1 ++ [b])) (v.1.2.1.length + 1))).isSome :=
    fun b ↦ primrec_isSome.comp (Code.primrec_evaln.comp ((hfuel.pair hcode).pair
      (Primrec₂.natPair.comp
        (Primrec.encode.comp (Primrec.list_append.comp hpref (Primrec.const [b]))) hlen)))
  exact Primrec₂.pair.comp
    (Primrec.list_append.comp hpref (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
    (Primrec.and.comp (Primrec.and.comp hflag (hev false)) (hev true))

theorem primrec_simOk : Primrec fun z : (Code × ℕ) × BitString ↦ simOk z.1.1 z.1.2 z.2 := by
  have hroot : Primrec fun z : (Code × ℕ) × BitString ↦
      (([], (Code.evaln z.1.2 z.1.1
        (Nat.pair (Encodable.encode ([] : BitString)) 0)).isSome) : BitString × Bool) :=
    Primrec₂.pair.comp (Primrec.const [])
      (primrec_isSome.comp (Code.primrec_evaln.comp
        (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.const (Nat.pair (Encodable.encode ([] : BitString)) 0)))))
  have hstep : Primrec₂ fun (z : (Code × ℕ) × BitString) (q : (BitString × Bool) × Bool) ↦
      simOkStep z.1.1 z.1.2 q.1 q.2 :=
    primrec_okStepFlat.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))
  exact Primrec.snd.comp (Primrec.list_foldl Primrec.snd hroot hstep)

/-- On input `encode σ`, the coded nonnegative rational the simulation assigns to `σ`. -/
def simEnum (p : Code) : ℕ →. ℕ := fun input ↦
  (Nat.rfind fun s ↦ Part.some
      (simOk p s ((Encodable.decode input : Option BitString).getD []))).map
    fun s ↦ RatCode.toNNRat (simAt p s ((Encodable.decode input : Option BitString).getD [])).2

/-- The uniform computability theorem; the fixed-program version is a corollary. -/
theorem partrec_simEnumUniform : Partrec fun z : Code × ℕ ↦ simEnum z.1 z.2 := by
  have hstr : Primrec fun z : Code × ℕ ↦ (Encodable.decode z.2 : Option BitString).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const [])
  have hok : Primrec fun q : (Code × ℕ) × ℕ ↦
      simOk q.1.1 q.2 ((Encodable.decode q.1.2 : Option BitString).getD []) :=
    primrec_simOk.comp
      (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair (hstr.comp Primrec.fst))
  have hval : Primrec fun q : (Code × ℕ) × ℕ ↦
      RatCode.toNNRat (simAt q.1.1 q.2 ((Encodable.decode q.1.2 : Option BitString).getD [])).2 :=
    RatCode.primrec_toNNRat.comp (Primrec.snd.comp (primrec_simAt.comp
      (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair (hstr.comp Primrec.fst))))
  exact Partrec.map (Partrec.rfind (Computable₂.partrec₂ hok.to_comp.to₂)) hval.to_comp.to₂

theorem partrec_simEnum (p : Code) : Nat.Partrec (simEnum p) :=
  Partrec.nat_iff.mp ((partrec_simEnumUniform.comp
    (Computable.pair (Computable.const p) Computable.id)).of_eq fun _ ↦ rfl)

/-! ## The resulting computable martingale -/

namespace ApproximableTreeMartingale

variable (D : ApproximableTreeMartingale)

theorem simEnum_dom (input : ℕ) : (simEnum D.approxCode.program input).Dom := by
  obtain ⟨s, hs⟩ := exists_simOk D.approxCode ((Encodable.decode input : Option BitString).getD [])
  obtain ⟨t, htmem, -⟩ := Nat.rfind_min'
    (p := fun s ↦ simOk D.approxCode.program s
      ((Encodable.decode input : Option BitString).getD []))
    (m := s) hs
  exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ htmem⟩

/-- The program computing the simulated capital. -/
noncomputable def simFunctionCode : NatFunctionCode :=
  NatFunctionCode.ofPartrecTotal (partrec_simEnum D.approxCode.program) D.simEnum_dom

theorem simFunctionCode_toFun (σ : BitString) :
    D.simFunctionCode.toFun (Encodable.encode σ)
      = RatCode.toNNRat (simCode D.approxCode σ) := by
  have hmem : D.simFunctionCode.toFun (Encodable.encode σ)
      ∈ simEnum D.approxCode.program (Encodable.encode σ) := by
    rw [simFunctionCode, NatFunctionCode.ofPartrecTotal_toFun]
    exact Part.get_mem _
  rw [simEnum, Encodable.encodek, Option.getD_some, Part.mem_map_iff] at hmem
  obtain ⟨s, hs, hval⟩ := hmem
  have hok : simOk D.approxCode.program s σ = true := by
    have := Nat.rfind_spec hs; simpa using this
  rw [← hval, simAt_eq D.approxCode hok, simCode]

/-- The bounded-error rational simulation of `D`. -/
noncomputable def simulate : ComputableMartingale where
  capital σ := NNRatCode.value (RatCode.toNNRat (simCode D.approxCode σ))
  fair σ := by
    -- reflect the exact signed fairness through `toNNRat`, licensed by `delta_nonneg`
    have hcast : ∀ τ : BitString,
        ((NNRatCode.value (RatCode.toNNRat (simCode D.approxCode τ)) : ℚ≥0) : ℚ)
          = simValue D.approxCode τ := fun τ ↦
      RatCode.value_toNNRat (simValue_nonneg (D := D) τ)
    have h := simValue_fair D.approxCode σ
    rw [← hcast, ← hcast, ← hcast] at h
    exact_mod_cast h
  program := D.simFunctionCode
  eval_capital σ := by rw [D.simFunctionCode_toFun σ]

@[simp] theorem simulate_capital (σ : BitString) :
    D.simulate.capital σ = NNRatCode.value (RatCode.toNNRat (simCode D.approxCode σ)) := rfl

/-- The simulated capital is exactly the signed value, using `delta_nonneg`. -/
theorem coe_simulate_capital (σ : BitString) :
    ((D.simulate.capital σ : ℚ≥0) : ℚ) = simValue D.approxCode σ :=
  RatCode.value_toNNRat (simValue_nonneg (D := D) σ)

/-- The simulation dominates the original martingale pointwise, so success transfers. -/
theorem simulate_ge (σ : BitString) : (D.capital σ : ℝ) ≤ ((D.simulate.capital σ : ℚ≥0) : ℝ) := by
  have hval : (((D.simulate.capital σ : ℚ≥0) : ℚ) : ℝ) = D.delta σ + (D.capital σ : ℝ) := by
    rw [coe_simulate_capital, simValue_eq]
  have hd := delta_nonneg (D := D) σ
  have : (((D.simulate.capital σ : ℚ≥0) : ℚ) : ℝ) = ((D.simulate.capital σ : ℚ≥0) : ℝ) := by
    push_cast; ring
  rw [← this, hval]
  linarith

/-- And exceeds it by at most `4`. -/
theorem simulate_le_add_four (σ : BitString) :
    ((D.simulate.capital σ : ℚ≥0) : ℝ) ≤ (D.capital σ : ℝ) + 4 := by
  have hval : (((D.simulate.capital σ : ℚ≥0) : ℚ) : ℝ) = D.delta σ + (D.capital σ : ℝ) := by
    rw [coe_simulate_capital, simValue_eq]
  have hd := delta_le_four (D := D) σ
  have : (((D.simulate.capital σ : ℚ≥0) : ℚ) : ℝ) = ((D.simulate.capital σ : ℚ≥0) : ℝ) := by
    push_cast; ring
  rw [← this, hval]
  linarith

end ApproximableTreeMartingale

end AlgorithmicRandomness
