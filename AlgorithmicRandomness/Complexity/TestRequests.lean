/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Complexity.KraftChaitin
import AlgorithmicRandomness.Randomness.MartinLof

/-!
# Kraft–Chaitin requests from a Martin-Löf test

A Martin-Löf test is turned into a request stream: at level `2 * n + 1`, each freshly enumerated
cylinder `τ` asks for a description of length `|τ| - n`. The odd reindexing is what makes the
total finite,

```text
∑ₙ 2ⁿ · μ(U_{2n+1})  ≤  ∑ₙ 2ⁿ · 2^-(2n+1)  =  ∑ₙ 2^-(n+1)  =  1,
```

whereas at level `n` every level would contribute a constant and the sum would diverge.

## Chronology versus level-major order

Execution is append-only and therefore chronological, while the weight bound groups requests by
their compression index `n`. These are different orders, and reconciling them after the fact would
mean a permutation argument. Instead the trace is built from *tagged events* — a private
`ℕ × KraftRequest` recording which level a request came from — and the tag is erased only at the
public boundary. List-prefix monotonicity is then definitional, while the proofs can still regroup
by level.

Fresh cylinders come from `FiniteOpenCode.difference`, so successive minimized stages are never
compared directly; a shorter cylinder replacing earlier longer ones would make historical request
weight overcount.
-/

open scoped NNRat

namespace AlgorithmicRandomness

open BitString

/-! ## The dyadic scaling identity

A request of length `|τ| - n` weighs `2ⁿ` times the cylinder it came from. Factored once, since
symbolic exponents do not survive `ring`. -/

theorem requestWeight_eq_scale {n : ℕ} {τ : BitString} (h : n ≤ τ.length) :
    (2⁻¹ : ℚ≥0) ^ (τ.length - n) = (2 : ℚ≥0) ^ n * BitString.weight τ := by
  have hsplit : (2⁻¹ : ℚ≥0) ^ (τ.length - n) * (2⁻¹ : ℚ≥0) ^ n = (2⁻¹ : ℚ≥0) ^ τ.length := by
    rw [← pow_add, show τ.length - n + n = τ.length from by omega]
  have hcancel : (2 : ℚ≥0) ^ n * (2⁻¹ : ℚ≥0) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [BitString.weight, ← hsplit,
    show (2 : ℚ≥0) ^ n * ((2⁻¹ : ℚ≥0) ^ (τ.length - n) * (2⁻¹ : ℚ≥0) ^ n)
      = ((2 : ℚ≥0) ^ n * (2⁻¹ : ℚ≥0) ^ n) * (2⁻¹ : ℚ≥0) ^ (τ.length - n) from by ring,
    hcancel, one_mul]

/-! ## The tagged event trace -/

/-- A request together with the level it came from. Private: the tag exists only so that the
weight proof can regroup an append-only trace by level. -/
private abbrev RequestEvent := ℕ × KraftRequest

/-- The level-`2n+1` source stage, as a list. -/
private def sourceStageList (T : MartinLofTest) (n s : ℕ) : List BitString :=
  stringStageList T.openCode.program (2 * n + 1) s

private theorem sourceStageList_toFinset (T : MartinLofTest) (n s : ℕ) :
    (sourceStageList T n s).toFinset = T.openCode.stage (2 * n + 1) s :=
  stringStageList_toFinset _ _ _

/-- The cylinders freshly enumerated at level `2n+1` when the global stage advances to `R`. At
`n = R` the level is introduced, so everything in its stage is fresh. -/
private def freshAt (T : MartinLofTest) (n R : ℕ) : List BitString :=
  if n = R then FiniteOpenCode.difference (sourceStageList T n R) []
  else FiniteOpenCode.difference (sourceStageList T n R) (sourceStageList T n (R - 1))

/-- The events emitted when the global stage advances to `R`: increments at every existing level,
and the whole of the newly introduced one. -/
private def eventsAt (T : MartinLofTest) (R : ℕ) : List RequestEvent :=
  (List.range (R + 1)).flatMap fun n ↦
    (freshAt T n R).map fun τ ↦ (n, (⟨τ.length - n, τ⟩ : KraftRequest))

private def eventTrace (T : MartinLofTest) : ℕ → List RequestEvent
  | 0 => eventsAt T 0
  | R + 1 => eventTrace T R ++ eventsAt T (R + 1)

@[simp] private theorem eventTrace_zero (T : MartinLofTest) :
    eventTrace T 0 = eventsAt T 0 := rfl

@[simp] private theorem eventTrace_succ (T : MartinLofTest) (R : ℕ) :
    eventTrace T (R + 1) = eventTrace T R ++ eventsAt T (R + 1) := rfl

private theorem eventTrace_prefix (T : MartinLofTest) {R R' : ℕ} (h : R ≤ R') :
    eventTrace T R <+: eventTrace T R' := by
  induction R' with
  | zero => rw [Nat.le_zero.mp h]
  | succ R' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans ⟨_, rfl⟩
    · exact List.prefix_refl _

/-- The public request list at global stage `R`, with the origin tags erased. -/
def requestTraceStage (T : MartinLofTest) (R : ℕ) : List KraftRequest :=
  (eventTrace T R).map Prod.snd

theorem requestTraceStage_prefix (T : MartinLofTest) {R R' : ℕ} (h : R ≤ R') :
    requestTraceStage T R <+: requestTraceStage T R' :=
  (eventTrace_prefix T h).map _

/-! ## Computability -/

private theorem primrec_sourceStageList (T : MartinLofTest) :
    Primrec₂ (sourceStageList T) := by
  refine (primrec_stringStageList.comp
    (Primrec.pair (Primrec.pair (Primrec.const T.openCode.program)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)))
      Primrec.snd)).of_eq fun z ↦ ?_
  rw [sourceStageList]

private theorem primrec_freshAt (T : MartinLofTest) : Primrec₂ (freshAt T) := by
  refine Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd) ?_ ?_
  · exact FiniteOpenCode.primrec_difference.comp
      (primrec_sourceStageList T |>.comp Primrec.fst Primrec.snd)
      (Primrec.const ([] : List BitString))
  · exact FiniteOpenCode.primrec_difference.comp
      (primrec_sourceStageList T |>.comp Primrec.fst Primrec.snd)
      (primrec_sourceStageList T |>.comp Primrec.fst
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))

private theorem primrec_eventsAt (T : MartinLofTest) : Primrec (eventsAt T) := by
  have hbody : Primrec₂ fun (R : ℕ) (n : ℕ) ↦
      (freshAt T n R).map fun τ ↦ (n, (⟨τ.length - n, τ⟩ : KraftRequest)) := by
    have hreq : Primrec fun w : (ℕ × ℕ) × BitString ↦
        (⟨w.2.length - w.1.2, w.2⟩ : KraftRequest) :=
      ((Primrec.of_equiv_symm_iff (e := KraftRequest.equivProd)).mpr
        (Primrec.pair
          (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
            (Primrec.snd.comp Primrec.fst))
          Primrec.snd)).of_eq fun _ ↦ rfl
    have hg : Primrec₂ fun (a : ℕ × ℕ) (τ : BitString) ↦
        (a.2, (⟨τ.length - a.2, τ⟩ : KraftRequest)) :=
      (Primrec.pair (Primrec.snd.comp Primrec.fst) hreq).to₂
    exact Primrec.list_map (primrec_freshAt T |>.comp Primrec.snd Primrec.fst) hg
  exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ) hbody

private theorem primrec_eventTrace (T : MartinLofTest) : Primrec (eventTrace T) := by
  have hstep : Primrec₂ fun (_ : ℕ) (p : ℕ × List RequestEvent) ↦
      p.2 ++ eventsAt T (p.1 + 1) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      ((primrec_eventsAt T).comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  refine (Primrec.nat_rec' Primrec.id ((primrec_eventsAt T).comp (Primrec.const 0))
    hstep).of_eq fun R ↦ ?_
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [eventTrace_succ, ← ih]
    rfl

theorem primrec_requestTraceStage (T : MartinLofTest) : Primrec (requestTraceStage T) :=
  Primrec.list_map (primrec_eventTrace T) (Primrec.snd.comp Primrec.snd).to₂

end AlgorithmicRandomness
