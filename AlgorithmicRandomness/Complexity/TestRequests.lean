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

open MeasureTheory
open scoped NNRat ENNReal

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

/-! ## The fixed-level partition

The outputs of the events tagged `n`, as a list. Two facts are proved together by induction on the
global stage, because the cross-incompatibility in the step case needs the set identity: old
outputs lie inside the old source stage, while every fresh output lies outside it, so their
cylinders are disjoint and hence the strings incompatible. -/

private def levelOutputs (T : MartinLofTest) : ℕ → ℕ → List BitString
  | 0, n => if n = 0 then freshAt T 0 0 else []
  | R + 1, n => levelOutputs T R n ++ (if n ≤ R + 1 then freshAt T n (R + 1) else [])

private theorem levelOutputs_succ (T : MartinLofTest) (R n : ℕ) :
    levelOutputs T (R + 1) n
      = levelOutputs T R n ++ (if n ≤ R + 1 then freshAt T n (R + 1) else []) := rfl

private theorem levelOutputs_eq_nil_of_lt (T : MartinLofTest) : ∀ {R n : ℕ}, R < n →
    levelOutputs T R n = [] := by
  intro R
  induction R with
  | zero => intro n h; rw [levelOutputs, if_neg (by omega)]
  | succ R ih =>
    intro n h
    rw [levelOutputs_succ, ih (by omega), if_neg (by omega), List.append_nil]

private theorem cylinderUnion_append (A B : List BitString) :
    cylinderUnion (A ++ B).toFinset
      = cylinderUnion A.toFinset ∪ cylinderUnion B.toFinset := by
  ext x
  simp only [mem_cylinderUnion, List.mem_toFinset, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨σ, hσ | hσ, hx⟩
    · exact Or.inl ⟨σ, hσ, hx⟩
    · exact Or.inr ⟨σ, hσ, hx⟩
  · rintro (⟨σ, hσ, hx⟩ | ⟨σ, hσ, hx⟩)
    · exact ⟨σ, Or.inl hσ, hx⟩
    · exact ⟨σ, Or.inr hσ, hx⟩

private theorem cylinderUnion_freshAt (T : MartinLofTest) (n R : ℕ) :
    cylinderUnion (freshAt T n R).toFinset
      = T.openCode.stageSet (2 * n + 1) R \
        (if n = R then ∅ else T.openCode.stageSet (2 * n + 1) (R - 1)) := by
  rw [freshAt]
  by_cases hnR : n = R
  · rw [if_pos hnR, if_pos hnR, FiniteOpenCode.cylinderUnion_difference,
      sourceStageList_toFinset, List.toFinset_nil, cylinderUnion_empty]
    rfl
  · rw [if_neg hnR, if_neg hnR, FiniteOpenCode.cylinderUnion_difference,
      sourceStageList_toFinset, sourceStageList_toFinset]
    rfl

/-- **The fixed-level invariant.** Proved with `levelOutputs_pairwise` by a single induction. -/
private theorem cylinderUnion_levelOutputs_and_pairwise (T : MartinLofTest) : ∀ (R n : ℕ),
    cylinderUnion (levelOutputs T R n).toFinset
        = (if n ≤ R then T.openCode.stageSet (2 * n + 1) R else ∅) ∧
      (levelOutputs T R n).Pairwise fun σ τ ↦ ¬BitString.Compatible σ τ := by
  intro R
  induction R with
  | zero =>
    intro n
    by_cases hn : n = 0
    · subst hn
      refine ⟨?_, ?_⟩
      · rw [levelOutputs, if_pos rfl, if_pos (le_refl 0),
          cylinderUnion_freshAt T 0 0, if_pos rfl, Set.sdiff_empty]
      · rw [levelOutputs, if_pos rfl, freshAt, if_pos rfl]
        exact FiniteOpenCode.pairwise_difference _ _
    · rw [levelOutputs, if_neg hn, if_neg (by omega), List.toFinset_nil, cylinderUnion_empty]
      exact ⟨rfl, List.Pairwise.nil⟩
  | succ R ih =>
    intro n
    by_cases hn : n ≤ R + 1
    · by_cases hnR : n = R + 1
      · subst hnR
        rw [levelOutputs_succ, levelOutputs_eq_nil_of_lt T (by omega), List.nil_append,
          if_pos (le_refl _)]
        refine ⟨?_, ?_⟩
        · rw [cylinderUnion_freshAt T (R + 1) (R + 1), if_pos rfl, Set.sdiff_empty,
            if_pos (le_refl _)]
        · rw [freshAt, if_pos rfl]
          exact FiniteOpenCode.pairwise_difference _ _
      · have hnle : n ≤ R := by omega
        obtain ⟨ihset, ihpw⟩ := ih n
        rw [if_pos hnle] at ihset
        have hfresh : cylinderUnion (freshAt T n (R + 1)).toFinset
            = T.openCode.stageSet (2 * n + 1) (R + 1) \ T.openCode.stageSet (2 * n + 1) R := by
          rw [cylinderUnion_freshAt T n (R + 1), if_neg hnR]
          norm_num
        have hsub : T.openCode.stageSet (2 * n + 1) R
            ⊆ T.openCode.stageSet (2 * n + 1) (R + 1) :=
          UniformOpenCode.stageSet_mono (Nat.le_succ R)
        refine ⟨?_, ?_⟩
        · rw [levelOutputs_succ, if_pos hn, cylinderUnion_append, ihset, hfresh, if_pos hn]
          exact Set.union_sdiff_cancel hsub
        · rw [levelOutputs_succ, if_pos hn]
          refine List.pairwise_append.mpr ⟨ihpw, ?_, ?_⟩
          · rw [freshAt, if_neg hnR]
            exact FiniteOpenCode.pairwise_difference _ _
          · intro a ha b hb
            rw [← disjoint_cylinder_iff]
            have hain : cylinder a ⊆ T.openCode.stageSet (2 * n + 1) R := by
              rw [← ihset]
              intro x hx
              exact mem_cylinderUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hx⟩
            have hbout : cylinder b
                ⊆ T.openCode.stageSet (2 * n + 1) (R + 1) \ T.openCode.stageSet (2 * n + 1) R := by
              rw [← hfresh]
              intro x hx
              exact mem_cylinderUnion.mpr ⟨b, List.mem_toFinset.mpr hb, hx⟩
            exact Set.disjoint_left.mpr fun x hxa hxb ↦ (hbout hxb).2 (hain hxa)
    · rw [levelOutputs_succ, levelOutputs_eq_nil_of_lt T (by omega), if_neg hn,
        if_neg (by omega), List.nil_append, List.toFinset_nil, cylinderUnion_empty]
      exact ⟨rfl, List.Pairwise.nil⟩

private theorem cylinderUnion_levelOutputs (T : MartinLofTest) {R n : ℕ} (h : n ≤ R) :
    cylinderUnion (levelOutputs T R n).toFinset = T.openCode.stageSet (2 * n + 1) R := by
  rw [(cylinderUnion_levelOutputs_and_pairwise T R n).1, if_pos h]

private theorem levelOutputs_pairwise (T : MartinLofTest) (R n : ℕ) :
    (levelOutputs T R n).Pairwise fun σ τ ↦ ¬BitString.Compatible σ τ :=
  (cylinderUnion_levelOutputs_and_pairwise T R n).2

private theorem nodup_levelOutputs (T : MartinLofTest) (R n : ℕ) :
    (levelOutputs T R n).Nodup := by
  refine List.Pairwise.imp ?_ (levelOutputs_pairwise T R n)
  intro a b hab heq
  subst heq
  exact hab (Or.inl (List.prefix_refl a))

/-! ## The representation seam

`levelOutputs` is defined by recursion on the global stage, which is what made the coupled
set/pairwise induction clean; the trace is a chronological list of tagged events. This is the one
place the two meet. Stating it for the *tagged requests* rather than only their outputs certifies
chronology, multiplicity, the edge cases, and the request length `|τ| - n` all at once — otherwise
the regrouping step would still need a separate theorem about lengths. -/

private theorem flatMap_ite (l : List ℕ) (n : ℕ) (L : List RequestEvent) (hnd : l.Nodup) :
    (l.flatMap fun m ↦ if m = n then L else []) = if n ∈ l then L else [] := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, ih hnd.2]
    by_cases hm : m = n
    · subst hm
      rw [if_pos rfl, if_neg hnd.1, if_pos List.mem_cons_self, List.append_nil]
    · rw [if_neg hm, List.nil_append]
      by_cases hmem : n ∈ l
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem m hmem)]
      · rw [if_neg hmem, if_neg (by simp [hmem, Ne.symm hm])]

private theorem filter_eventsAt (T : MartinLofTest) (R n : ℕ) :
    (eventsAt T R).filter (fun e ↦ decide (e.1 = n))
      = if n ≤ R then (freshAt T n R).map fun τ ↦ ((n, ⟨τ.length - n, τ⟩) : RequestEvent)
        else [] := by
  rw [eventsAt, List.filter_flatMap]
  have hbody : ∀ m ∈ List.range (R + 1),
      (((freshAt T m R).map fun τ ↦ ((m, ⟨τ.length - m, τ⟩) : RequestEvent)).filter
        fun e ↦ decide (e.1 = n))
        = if m = n then
            (freshAt T n R).map fun τ ↦ ((n, ⟨τ.length - n, τ⟩) : RequestEvent) else [] := by
    intro m _
    rw [List.filter_map]
    by_cases hm : m = n
    · subst hm
      rw [if_pos rfl, List.filter_congr (q := fun _ ↦ true) (fun _ _ ↦ by simp),
        List.filter_true]
    · rw [if_neg hm, List.filter_congr (q := fun _ ↦ false) (fun _ _ ↦ by simp [hm]),
        List.filter_false, List.map_nil]
  rw [List.flatMap_congr hbody, flatMap_ite _ _ _ List.nodup_range]
  by_cases h : n ≤ R
  · rw [if_pos (List.mem_range.mpr (Nat.lt_succ_of_le h)), if_pos h]
  · rw [if_neg (fun hc ↦ h (Nat.lt_succ_iff.mp (List.mem_range.mp hc))), if_neg h]

private theorem filter_eventTrace_eq_levelRequests (T : MartinLofTest) (R n : ℕ) :
    (eventTrace T R).filter (fun e ↦ decide (e.1 = n))
      = (levelOutputs T R n).map fun τ ↦ ((n, ⟨τ.length - n, τ⟩) : RequestEvent) := by
  induction R with
  | zero =>
    rw [eventTrace_zero, filter_eventsAt, levelOutputs]
    by_cases hn : n = 0
    · subst hn
      rw [if_pos (le_refl 0), if_pos rfl]
    · rw [if_neg (by omega), if_neg hn, List.map_nil]
  | succ R ih =>
    rw [eventTrace_succ, List.filter_append, ih, filter_eventsAt, levelOutputs_succ,
      List.map_append]
    by_cases hn : n ≤ R + 1
    · rw [if_pos hn, if_pos hn]
    · rw [if_neg hn, if_neg hn, List.map_nil]

/-- The output form, as a corollary. -/
private theorem filter_eventTrace_map_output (T : MartinLofTest) (R n : ℕ) :
    ((eventTrace T R).filter (fun e ↦ decide (e.1 = n))).map (fun e ↦ e.2.output)
      = levelOutputs T R n := by
  rw [filter_eventTrace_eq_levelRequests, List.map_map]
  exact List.map_id _

/-! ## Step 1: the output-weight identity -/

private theorem weight_le_listWeight : ∀ {L : List BitString} {τ : BitString}, τ ∈ L →
    BitString.weight τ ≤ listWeight L := by
  intro L
  induction L with
  | nil => intro τ h; exact absurd h (by simp)
  | cons a L ih =>
    intro τ h
    rw [listWeight_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_self_add
    · exact (ih h').trans le_add_self

private theorem prefixFree_levelOutputs (T : MartinLofTest) (R n : ℕ) :
    PrefixFree ((levelOutputs T R n).toFinset : Set BitString) := by
  rw [prefixFree_iff]
  intro σ hσ τ hτ hpre
  rw [Finset.mem_coe, List.mem_toFinset] at hσ hτ
  by_contra hne
  exact pairwise_incompat_pair (levelOutputs_pairwise T R n) hσ hτ hne (Or.inl hpre)

private theorem coe_pow_inv_two' (k : ℕ) :
    (((2⁻¹ : ℚ≥0) ^ k : ℚ≥0) : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) ^ k := by
  rw [← ENNReal.coe_nnratCast]
  push_cast
  rfl

private theorem listWeight_levelOutputs (T : MartinLofTest) (R n : ℕ) :
    listWeight (levelOutputs T R n)
      = if n ≤ R then T.openCode.stageWeight (2 * n + 1) R else 0 := by
  by_cases hn : n ≤ R
  · rw [if_pos hn, ← listWeight_toFinset (nodup_levelOutputs T R n)]
    have hmeas : fairCoin (cylinderUnion (levelOutputs T R n).toFinset)
        = ((totalWeight (levelOutputs T R n).toFinset : ℚ≥0) : ℝ≥0∞) :=
      fairCoin_cylinderUnion_of_prefixFree (prefixFree_levelOutputs T R n)
    rw [cylinderUnion_levelOutputs T hn] at hmeas
    have hstage : fairCoin (T.openCode.stageSet (2 * n + 1) R)
        = ((T.openCode.stageWeight (2 * n + 1) R : ℚ≥0) : ℝ≥0∞) :=
      UniformOpenCode.fairCoin_stageSet T.openCode (2 * n + 1) R
    rw [hstage] at hmeas
    rw [← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast, ENNReal.coe_inj] at hmeas
    exact_mod_cast hmeas.symm
  · rw [if_neg hn, levelOutputs_eq_nil_of_lt T (by omega), listWeight_nil]

/-! ## Step 2: reflecting the order of half-powers -/

private theorem half_pow_lt_half_pow_succ (a : ℕ) :
    (2⁻¹ : ℚ≥0) ^ (a + 1) < (2⁻¹ : ℚ≥0) ^ a := by
  have hpos : (0 : ℚ≥0) < (2⁻¹ : ℚ≥0) ^ a := by positivity
  calc (2⁻¹ : ℚ≥0) ^ (a + 1) = (2⁻¹ : ℚ≥0) ^ a * 2⁻¹ := pow_succ _ _
    _ < (2⁻¹ : ℚ≥0) ^ a * 1 := mul_lt_mul_of_pos_left (by norm_num) hpos
    _ = (2⁻¹ : ℚ≥0) ^ a := mul_one _

theorem half_pow_le_half_pow_iff {a b : ℕ} :
    (2⁻¹ : ℚ≥0) ^ a ≤ (2⁻¹ : ℚ≥0) ^ b ↔ b ≤ a := by
  constructor
  · intro h
    by_contra hab
    push Not at hab
    obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
    have h1 : (2⁻¹ : ℚ≥0) ^ (a + 1 + d) ≤ (2⁻¹ : ℚ≥0) ^ (a + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact absurd h (not_le.mpr (lt_of_le_of_lt h1 (half_pow_lt_half_pow_succ a)))
  · intro h
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-! ## Step 3: length admissibility

A fresh cylinder at level `2n+1` cannot be shorter than `2n+1`: its own weight is at most the
stage weight, which the test bounds by `2⁻⁽²ⁿ⁺¹⁾`. This is where measure theory enters, and it
does not appear again. -/

private theorem stageWeight_le (T : MartinLofTest) (k s : ℕ) :
    T.openCode.stageWeight k s ≤ (2⁻¹ : ℚ≥0) ^ k := by
  have h := (UniformOpenCode.fairCoin_denote_le_iff T.openCode k _).mp (T.measure_le k) s
  rw [← coe_pow_inv_two' k, ← ENNReal.coe_nnratCast, ← ENNReal.coe_nnratCast,
    ENNReal.coe_le_coe] at h
  exact_mod_cast h

private theorem length_ge_of_mem_levelOutputs (T : MartinLofTest) {R n : ℕ} (hn : n ≤ R)
    {τ : BitString} (hτ : τ ∈ levelOutputs T R n) : 2 * n + 1 ≤ τ.length := by
  have h1 : BitString.weight τ ≤ listWeight (levelOutputs T R n) := weight_le_listWeight hτ
  rw [listWeight_levelOutputs, if_pos hn] at h1
  have h2 : BitString.weight τ ≤ (2⁻¹ : ℚ≥0) ^ (2 * n + 1) :=
    h1.trans (stageWeight_le T _ _)
  rw [BitString.weight] at h2
  exact half_pow_le_half_pow_iff.mp h2

private theorem le_length_of_mem_levelOutputs (T : MartinLofTest) {R n : ℕ} (hn : n ≤ R)
    {τ : BitString} (hτ : τ ∈ levelOutputs T R n) : n ≤ τ.length :=
  le_trans (by omega) (length_ge_of_mem_levelOutputs T hn hτ)

/-! ## Step 4: request scaling -/

private theorem two_pow_mul_half_pow (n : ℕ) :
    (2 : ℚ≥0) ^ n * (2⁻¹ : ℚ≥0) ^ (2 * n + 1) = (2⁻¹ : ℚ≥0) ^ (n + 1) := by
  have hsplit : (2⁻¹ : ℚ≥0) ^ (2 * n + 1) = (2⁻¹ : ℚ≥0) ^ n * (2⁻¹ : ℚ≥0) ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hcancel : (2 : ℚ≥0) ^ n * (2⁻¹ : ℚ≥0) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hsplit, ← mul_assoc, hcancel, one_mul]

private theorem totalRequestWeight_map_eq_scale : ∀ {L : List BitString} {n : ℕ},
    (∀ τ ∈ L, n ≤ τ.length) →
    totalRequestWeight (L.map fun τ ↦ (⟨τ.length - n, τ⟩ : KraftRequest))
      = (2 : ℚ≥0) ^ n * listWeight L := by
  intro L
  induction L with
  | nil => intro n _; rw [List.map_nil, totalRequestWeight_nil, listWeight_nil, mul_zero]
  | cons a L ih =>
    intro n h
    rw [List.map_cons, totalRequestWeight, List.map_cons, List.sum_cons, ← totalRequestWeight,
      ih (fun τ hτ ↦ h τ (List.mem_cons_of_mem a hτ)), listWeight_cons, mul_add]
    congr 1
    rw [KraftRequest.weight]
    exact requestWeight_eq_scale (h a List.mem_cons_self)

private theorem levelRequestWeight_eq_scale (T : MartinLofTest) {R n : ℕ} (hn : n ≤ R) :
    totalRequestWeight ((levelOutputs T R n).map fun τ ↦ (⟨τ.length - n, τ⟩ : KraftRequest))
      = (2 : ℚ≥0) ^ n * listWeight (levelOutputs T R n) :=
  totalRequestWeight_map_eq_scale fun _ hτ ↦ le_length_of_mem_levelOutputs T hn hτ

/-! ## Step 5: the level bound -/

private theorem levelRequestWeight_le (T : MartinLofTest) (R n : ℕ) :
    totalRequestWeight ((levelOutputs T R n).map fun τ ↦ (⟨τ.length - n, τ⟩ : KraftRequest))
      ≤ (2⁻¹ : ℚ≥0) ^ (n + 1) := by
  by_cases hn : n ≤ R
  · rw [levelRequestWeight_eq_scale T hn, listWeight_levelOutputs, if_pos hn]
    calc (2 : ℚ≥0) ^ n * T.openCode.stageWeight (2 * n + 1) R
        ≤ (2 : ℚ≥0) ^ n * (2⁻¹ : ℚ≥0) ^ (2 * n + 1) :=
          mul_le_mul' le_rfl (stageWeight_le T _ _)
      _ = (2⁻¹ : ℚ≥0) ^ (n + 1) := two_pow_mul_half_pow n
  · rw [levelOutputs_eq_nil_of_lt T (by omega), List.map_nil, totalRequestWeight_nil]
    exact zero_le

/-! ## Step 6: regrouping

Only the tag index becomes a `Finset`; every event group stays a `List`. Identical requests can
occur at different chronological positions, and turning the trace itself into a `Finset` would
deduplicate them and corrupt the accounting. -/

private theorem eventTag_le (T : MartinLofTest) : ∀ {R : ℕ} {e : RequestEvent},
    e ∈ eventTrace T R → e.1 ≤ R := by
  intro R
  induction R with
  | zero =>
    intro e he
    rw [eventTrace_zero, eventsAt, List.mem_flatMap] at he
    obtain ⟨m, hm, hme⟩ := he
    rw [List.mem_range] at hm
    rw [List.mem_map] at hme
    obtain ⟨τ, -, rfl⟩ := hme
    omega
  | succ R ih =>
    intro e he
    rw [eventTrace_succ, List.mem_append] at he
    rcases he with he' | he'
    · exact (ih he').trans (Nat.le_succ R)
    · rw [eventsAt, List.mem_flatMap] at he'
      obtain ⟨m, hm, hme⟩ := he'
      rw [List.mem_range] at hm
      rw [List.mem_map] at hme
      obtain ⟨τ, -, rfl⟩ := hme
      omega

private theorem totalRequestWeight_regroup : ∀ {L : List RequestEvent} {R : ℕ},
    (∀ e ∈ L, e.1 ≤ R) →
    totalRequestWeight (L.map Prod.snd)
      = ∑ n ∈ Finset.range (R + 1),
          totalRequestWeight ((L.filter fun e ↦ decide (e.1 = n)).map Prod.snd) := by
  intro L
  induction L with
  | nil =>
    intro R _
    rw [List.map_nil, totalRequestWeight_nil]
    simp
  | cons e L ih =>
    intro R h
    have hstep : ∀ n : ℕ,
        totalRequestWeight (((e :: L).filter fun f ↦ decide (f.1 = n)).map Prod.snd)
          = (if e.1 = n then e.2.weight else 0)
            + totalRequestWeight ((L.filter fun f ↦ decide (f.1 = n)).map Prod.snd) := by
      intro n
      rw [List.filter_cons]
      by_cases he : e.1 = n
      · rw [if_pos (by simp [he]), if_pos he, List.map_cons, totalRequestWeight, List.map_cons,
          List.sum_cons, ← totalRequestWeight]
      · rw [if_neg (by simp [he]), if_neg he, zero_add]
    rw [List.map_cons, totalRequestWeight, List.map_cons, List.sum_cons, ← totalRequestWeight,
      ih fun f hf ↦ h f (List.mem_cons_of_mem e hf), Finset.sum_congr rfl (fun n _ ↦ hstep n),
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq (Finset.range (R + 1)) e.1 (fun _ ↦ e.2.weight),
      if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (h e List.mem_cons_self)))]

private theorem totalRequestWeight_requestTraceStage (T : MartinLofTest) (R : ℕ) :
    totalRequestWeight (requestTraceStage T R)
      = ∑ n ∈ Finset.range (R + 1),
          totalRequestWeight ((levelOutputs T R n).map
            fun τ ↦ (⟨τ.length - n, τ⟩ : KraftRequest)) := by
  rw [requestTraceStage, totalRequestWeight_regroup (fun e he ↦ eventTag_le T he)]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [filter_eventTrace_eq_levelRequests, List.map_map]
  rfl

private theorem geom_half_sum_add (N : ℕ) :
    (∑ n ∈ Finset.range N, (2⁻¹ : ℚ≥0) ^ (n + 1)) + (2⁻¹ : ℚ≥0) ^ N = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, pow_succ_add_pow_succ, ih]

theorem totalRequestWeight_requestTraceStage_le (T : MartinLofTest) (R : ℕ) :
    totalRequestWeight (requestTraceStage T R) ≤ 1 := by
  rw [totalRequestWeight_requestTraceStage]
  calc ∑ n ∈ Finset.range (R + 1),
        totalRequestWeight ((levelOutputs T R n).map fun τ ↦ (⟨τ.length - n, τ⟩ : KraftRequest))
      ≤ ∑ n ∈ Finset.range (R + 1), (2⁻¹ : ℚ≥0) ^ (n + 1) :=
        Finset.sum_le_sum fun n _ ↦ levelRequestWeight_le T R n
    _ ≤ (∑ n ∈ Finset.range (R + 1), (2⁻¹ : ℚ≥0) ^ (n + 1)) + (2⁻¹ : ℚ≥0) ^ (R + 1) := le_self_add
    _ = 1 := geom_half_sum_add (R + 1)

/-! ## The trace, and coverage -/

/-- **The request trace of a Martin-Löf test.** -/
def MartinLofTest.kraftRequestTrace (T : MartinLofTest) : KraftRequestTrace where
  stage := requestTraceStage T
  stage_prefix := fun h ↦ requestTraceStage_prefix T h
  primrec_stage := primrec_requestTraceStage T
  weight_le := totalRequestWeight_requestTraceStage_le T

/-- The common core of the coverage theorems: a captured point lies in a requested cylinder whose
length the accounting already bounded below. -/
private theorem exists_levelOutput_of_mem_denote (T : MartinLofTest) {x : Cantor} {n : ℕ}
    (hx : x ∈ T.openCode.denote (2 * n + 1)) :
    ∃ (R : ℕ) (τ : BitString), τ ∈ levelOutputs T R n ∧ x ∈ cylinder τ ∧ n ≤ τ.length := by
  obtain ⟨s, hs⟩ := UniformOpenCode.mem_denote.mp hx
  have hxR : x ∈ T.openCode.stageSet (2 * n + 1) (max n s) :=
    UniformOpenCode.stageSet_mono (le_max_right n s) hs
  rw [← cylinderUnion_levelOutputs T (le_max_left n s)] at hxR
  obtain ⟨τ, hτ, hxτ⟩ := mem_cylinderUnion.mp hxR
  rw [List.mem_toFinset] at hτ
  exact ⟨max n s, τ, hτ, hxτ, le_length_of_mem_levelOutputs T (le_max_left n s) hτ⟩

private theorem mem_stage_of_mem_levelOutputs (T : MartinLofTest) {R n : ℕ} {τ : BitString}
    (hτ : τ ∈ levelOutputs T R n) :
    (⟨τ.length - n, τ⟩ : KraftRequest) ∈ T.kraftRequestTrace.stage R := by
  have hev : ((n, (⟨τ.length - n, τ⟩ : KraftRequest)) : RequestEvent)
      ∈ (eventTrace T R).filter fun e ↦ decide (e.1 = n) := by
    rw [filter_eventTrace_eq_levelRequests]
    exact List.mem_map_of_mem hτ
  exact List.mem_map_of_mem (List.mem_of_mem_filter hev)

/-- **Coverage.** Every point captured at level `2n+1` lies inside a cylinder that was requested,
at exactly the length the accounting assumed. This is the seam from captured points to short
machine descriptions. -/
theorem exists_request_of_mem_denote (T : MartinLofTest) {x : Cantor} {n : ℕ}
    (hx : x ∈ T.openCode.denote (2 * n + 1)) :
    ∃ r : KraftRequest, (∃ R, r ∈ T.kraftRequestTrace.stage R) ∧
      x ∈ cylinder r.output ∧ r.length = r.output.length - n := by
  obtain ⟨R, τ, hτ, hxτ, -⟩ := exists_levelOutput_of_mem_denote T hx
  exact ⟨⟨τ.length - n, τ⟩, ⟨R, mem_stage_of_mem_levelOutputs T hτ⟩, hxτ, rfl⟩

/-- The subtraction-free form. `ℕ` subtraction truncates, so downstream arithmetic wants this one:
the length bound proved during the partition is exactly what cancels it. -/
theorem exists_request_of_mem_denote_add (T : MartinLofTest) {x : Cantor} {n : ℕ}
    (hx : x ∈ T.openCode.denote (2 * n + 1)) :
    ∃ r : KraftRequest, (∃ R, r ∈ T.kraftRequestTrace.stage R) ∧
      x ∈ cylinder r.output ∧ r.length + n = r.output.length := by
  obtain ⟨R, τ, hτ, hxτ, hlen⟩ := exists_levelOutput_of_mem_denote T hx
  exact ⟨⟨τ.length - n, τ⟩, ⟨R, mem_stage_of_mem_levelOutputs T hτ⟩, hxτ,
    Nat.sub_add_cancel hlen⟩

end AlgorithmicRandomness
