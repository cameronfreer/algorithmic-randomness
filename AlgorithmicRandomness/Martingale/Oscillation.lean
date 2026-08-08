/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.RatCode
import AlgorithmicRandomness.Martingale.Savings

/-!
# The bounded oscillating martingale

From a martingale with the savings property, build a bounded one that oscillates between values
at most `2` and values at least `3` along every path where the source succeeds. This converts
*divergence* of the source into *bounded oscillation*, which is what a Lipschitz function's
slope process can exhibit.

Following Freer–Kjos-Hanssen–Nies–Stephan, Theorem 4.2. The construction is a single martingale
carrying a phase bit, updated **additively** by the source's capital increment: in the up phase
it adds what the source risks until reaching `3`, in the down phase it subtracts until reaching
`2`, clipping exactly at the threshold and sending the clipped child into the opposite phase.

The four constants are not interchangeable. A fair martingale confined to `[c, d]` that
*attains* an endpoint is frozen there — both children must average to the endpoint while
staying inside — so it could never oscillate. Here the oscillation targets `2` and `3` are
interior to the hard bounds `[1, 4]`, which is exactly what leaves room to keep moving. The
bounds themselves come from the savings property, not from positivity.

## Representation

The recursion is stated on `ℚ`, not `ℚ≥0`: the update subtracts, and truncated subtraction
would contaminate every semantic proof. The nonnegativity needed to package the result is a
*theorem* about the raw recursion, proved from the bounds.
-/

open scoped NNRat

namespace AlgorithmicRandomness

/-- The source capital as a signed rational. -/
def srcCapital (M : TreeMartingale) (σ : BitString) : ℚ := ((M.capital σ : ℚ≥0) : ℚ)

/-- The capital increment of `M` at `σ` on bit `b`, as a signed rational. -/
def increment (M : TreeMartingale) (σ : BitString) (b : Bool) : ℚ :=
  srcCapital M (σ ++ [b]) - srcCapital M σ

theorem srcCapital_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    srcCapital M (σ ++ [b]) = srcCapital M σ + increment M σ b := by
  rw [increment]; ring

/-- The two increments cancel, because the source is a martingale. -/
theorem increment_add (M : TreeMartingale) (σ : BitString) :
    increment M σ false + increment M σ true = 0 := by
  have h : srcCapital M (σ ++ [false]) + srcCapital M (σ ++ [true]) = 2 * srcCapital M σ := by
    rw [srcCapital, srcCapital, srcCapital]; exact_mod_cast M.fair σ
  rw [increment, increment]
  linarith

theorem increment_neg (M : TreeMartingale) (σ : BitString) (b : Bool) :
    increment M σ (!b) = -increment M σ b := by
  have h := increment_add M σ
  cases b <;> simp only [Bool.not_false, Bool.not_true] <;> linarith

/-! ## The raw recursion

Each step is local in the bit: the sibling's value is `2 v - r`, so whether the sibling clips
is decidable from `r` and `v` alone. -/

/-- One step. The phase is `true` for up, `false` for down. -/
def oscStep (M : TreeMartingale) (q : BitString × ℚ × Bool) (b : Bool) : BitString × ℚ × Bool :=
  if q.2.2 then
    -- up phase: this child's value is `v + d`, the sibling's is `v - d`
    if 3 ≤ q.2.1 + increment M q.1 b then (q.1 ++ [b], 3, false)
    else if 3 ≤ q.2.1 - increment M q.1 b then (q.1 ++ [b], 2 * q.2.1 - 3, true)
    else (q.1 ++ [b], q.2.1 + increment M q.1 b, true)
  else
    -- down phase: this child's value is `v - d`, the sibling's is `v + d`
    if q.2.1 - increment M q.1 b ≤ 2 then (q.1 ++ [b], 2, true)
    else if q.2.1 + increment M q.1 b ≤ 2 then (q.1 ++ [b], 2 * q.2.1 - 2, false)
    else (q.1 ++ [b], q.2.1 - increment M q.1 b, false)

def oscPair (M : TreeMartingale) (σ : BitString) : BitString × ℚ × Bool :=
  σ.foldl (oscStep M) ([], (2, true))

/-- The value of the oscillating martingale at `σ`, before any conversion. -/
def rawValue (M : TreeMartingale) (σ : BitString) : ℚ := (oscPair M σ).2.1

/-- The phase at `σ`: `true` is the up phase, `false` the down phase. -/
def phase (M : TreeMartingale) (σ : BitString) : Bool := (oscPair M σ).2.2

/-- Every branch of the step extends the prefix by the bit. -/
theorem oscStep_fst (M : TreeMartingale) (q : BitString × ℚ × Bool) (b : Bool) :
    (oscStep M q b).1 = q.1 ++ [b] := by
  rw [oscStep]
  split
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem foldl_oscStep_fst (M : TreeMartingale) (σ : BitString) :
    ∀ (τ : BitString) (q : ℚ × Bool), (σ.foldl (oscStep M) (τ, q)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ q; simp
  | cons b σ ih =>
    intro τ q
    rw [List.foldl_cons, ih, oscStep_fst]
    simp

@[simp] theorem oscPair_fst (M : TreeMartingale) (σ : BitString) : (oscPair M σ).1 = σ := by
  rw [oscPair, foldl_oscStep_fst, List.nil_append]

theorem oscPair_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    oscPair M (σ ++ [b]) = oscStep M (oscPair M σ) b := by
  rw [oscPair, oscPair, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem rawValue_nil (M : TreeMartingale) : rawValue M [] = 2 := rfl
@[simp] theorem phase_nil (M : TreeMartingale) : phase M [] = true := rfl

/-- The step, written out at `σ ++ [b]`. -/
theorem oscPair_append_eq (M : TreeMartingale) (σ : BitString) (b : Bool) :
    (rawValue M (σ ++ [b]), phase M (σ ++ [b]))
      = (if phase M σ then
          (if 3 ≤ rawValue M σ + increment M σ b then ((3 : ℚ), false)
           else if 3 ≤ rawValue M σ - increment M σ b then (2 * rawValue M σ - 3, true)
           else (rawValue M σ + increment M σ b, true))
        else
          (if rawValue M σ - increment M σ b ≤ 2 then ((2 : ℚ), true)
           else if rawValue M σ + increment M σ b ≤ 2 then (2 * rawValue M σ - 2, false)
           else (rawValue M σ - increment M σ b, false))) := by
  have h : oscPair M (σ ++ [b]) = oscStep M (oscPair M σ) b := oscPair_append M σ b
  unfold rawValue phase
  rw [h, oscStep, oscPair_fst]
  split
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl

/-! ## The phase invariant

Fairness is *not* available for an arbitrary state: in the up phase with `v = 4` and zero
increment, both children would clip to `3`, giving `6 ≠ 8`. What excludes this is the threshold
component below — an up-phase value is always `< 3`, so `r₀ + r₁ = 2v < 6` and at most one child
can cross. The invariant must therefore be proved before fairness, not after.

The history component carries a witness of the last phase switch, stated without subtraction.
It says the oscillator has gained at least as much as the source since that switch, which is
exactly what the savings property converts into the `[1, 4]` bounds. -/

/-- The threshold and history invariant at `σ`. -/
def PhaseInv (M : TreeMartingale) (σ : BitString) : Prop :=
  if phase M σ then
    rawValue M σ < 3 ∧ ∃ ρ, ρ <+: σ ∧ rawValue M ρ = 2 ∧
      2 + srcCapital M σ ≤ rawValue M σ + srcCapital M ρ
  else
    2 < rawValue M σ ∧ ∃ ρ, ρ <+: σ ∧ rawValue M ρ = 3 ∧
      rawValue M σ + srcCapital M σ ≤ 3 + srcCapital M ρ

theorem phaseInv (M : TreeMartingale) (σ : BitString) : PhaseInv M σ := by
  induction σ using List.reverseRecOn with
  | nil =>
    rw [PhaseInv, phase_nil, if_pos rfl, rawValue_nil]
    exact ⟨by norm_num, [], List.nil_prefix, rawValue_nil M, by norm_num⟩
  | append_singleton σ b ih =>
    have hstep := oscPair_append_eq M σ b
    rw [PhaseInv] at ih ⊢
    by_cases hph : phase M σ = true
    · -- up phase at `σ`
      rw [if_pos hph] at ih hstep
      obtain ⟨hlt, ρ, hρpre, hρval, hρineq⟩ := ih
      by_cases h1 : 3 ≤ rawValue M σ + increment M σ b
      · -- this child clips at `3` and switches down; it is its own witness
        rw [if_pos h1] at hstep
        obtain ⟨hv, hp⟩ := Prod.mk.injEq .. ▸ hstep
        rw [hp, if_neg (by simp)]
        refine ⟨by rw [hv]; norm_num, σ ++ [b], List.prefix_refl _, hv, ?_⟩
        rw [hv]
      · rw [if_neg h1] at hstep
        by_cases h2 : 3 ≤ rawValue M σ - increment M σ b
        · -- the sibling clips; this child is raised to `2 v - 3` and stays up
          rw [if_pos h2] at hstep
          obtain ⟨hv, hp⟩ := Prod.mk.injEq .. ▸ hstep
          rw [hp, if_pos rfl]
          refine ⟨by rw [hv]; linarith, ρ, hρpre.trans (List.prefix_append σ [b]), hρval, ?_⟩
          rw [hv, srcCapital_append]
          linarith
        · -- neither clips
          rw [if_neg h2] at hstep
          obtain ⟨hv, hp⟩ := Prod.mk.injEq .. ▸ hstep
          rw [hp, if_pos rfl]
          refine ⟨by rw [hv]; linarith, ρ, hρpre.trans (List.prefix_append σ [b]), hρval, ?_⟩
          rw [hv, srcCapital_append]
          linarith
    · -- down phase at `σ`
      rw [Bool.not_eq_true] at hph
      rw [if_neg (by simp [hph])] at ih
      rw [if_neg (by simp [hph])] at hstep
      obtain ⟨hgt, ρ, hρpre, hρval, hρineq⟩ := ih
      by_cases h1 : rawValue M σ - increment M σ b ≤ 2
      · rw [if_pos h1] at hstep
        obtain ⟨hv, hp⟩ := Prod.mk.injEq .. ▸ hstep
        rw [hp, if_pos rfl]
        refine ⟨by rw [hv]; norm_num, σ ++ [b], List.prefix_refl _, hv, ?_⟩
        rw [hv]
      · rw [if_neg h1] at hstep
        by_cases h2 : rawValue M σ + increment M σ b ≤ 2
        · rw [if_pos h2] at hstep
          obtain ⟨hv, hp⟩ := Prod.mk.injEq .. ▸ hstep
          rw [hp, if_neg (by simp)]
          refine ⟨by rw [hv]; linarith, ρ, hρpre.trans (List.prefix_append σ [b]), hρval, ?_⟩
          rw [hv, srcCapital_append]
          linarith
        · rw [if_neg h2] at hstep
          obtain ⟨hv, hp⟩ := Prod.mk.injEq .. ▸ hstep
          rw [hp, if_neg (by simp)]
          refine ⟨by rw [hv]; linarith, ρ, hρpre.trans (List.prefix_append σ [b]), hρval, ?_⟩
          rw [hv, srcCapital_append]
          linarith

theorem rawValue_lt_three (M : TreeMartingale) {σ : BitString} (h : phase M σ = true) :
    rawValue M σ < 3 := by
  have := phaseInv M σ
  rw [PhaseInv, if_pos h] at this
  exact this.1

theorem two_lt_rawValue (M : TreeMartingale) {σ : BitString} (h : phase M σ = false) :
    2 < rawValue M σ := by
  have := phaseInv M σ
  rw [PhaseInv, if_neg (by simp [h])] at this
  exact this.1

/-! ## Crossing uniqueness and fairness -/

theorem rawValue_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    rawValue M (σ ++ [b])
      = if phase M σ then
          (if 3 ≤ rawValue M σ + increment M σ b then 3
           else if 3 ≤ rawValue M σ - increment M σ b then 2 * rawValue M σ - 3
           else rawValue M σ + increment M σ b)
        else
          (if rawValue M σ - increment M σ b ≤ 2 then 2
           else if rawValue M σ + increment M σ b ≤ 2 then 2 * rawValue M σ - 2
           else rawValue M σ - increment M σ b) := by
  have h := congrArg Prod.fst (oscPair_append_eq M σ b)
  simpa only [apply_ite Prod.fst] using h

theorem phase_append (M : TreeMartingale) (σ : BitString) (b : Bool) :
    phase M (σ ++ [b])
      = if phase M σ then
          (if 3 ≤ rawValue M σ + increment M σ b then false else true)
        else
          (if rawValue M σ - increment M σ b ≤ 2 then true else false) := by
  have h := congrArg Prod.snd (oscPair_append_eq M σ b)
  simpa only [apply_ite Prod.snd, ite_self] using h

/-- **Crossing uniqueness.** In the up phase the two candidate values sum to `2 v < 6`, so at
most one can reach `3`; dually in the down phase. This is what makes the clipping rule
consistent, and hence what makes the recursion fair. -/
theorem not_both_cross_up (M : TreeMartingale) {σ : BitString} (h : phase M σ = true) :
    ¬(3 ≤ rawValue M σ + increment M σ false ∧ 3 ≤ rawValue M σ + increment M σ true) := by
  rintro ⟨h0, h1⟩
  have hsum := increment_add M σ
  have := rawValue_lt_three M h
  linarith

theorem not_both_cross_down (M : TreeMartingale) {σ : BitString} (h : phase M σ = false) :
    ¬(rawValue M σ - increment M σ false ≤ 2 ∧ rawValue M σ - increment M σ true ≤ 2) := by
  rintro ⟨h0, h1⟩
  have hsum := increment_add M σ
  have := two_lt_rawValue M h
  linarith

/-- **Exact fairness**, available only once crossing uniqueness rules out the double-clip. -/
theorem rawValue_fair (M : TreeMartingale) (σ : BitString) :
    rawValue M (σ ++ [false]) + rawValue M (σ ++ [true]) = 2 * rawValue M σ := by
  have hf := rawValue_append M σ false
  have ht := rawValue_append M σ true
  have hsum := increment_add M σ
  by_cases hph : phase M σ = true
  · rw [if_pos hph] at hf ht
    have huniq := not_both_cross_up M hph
    by_cases h0 : 3 ≤ rawValue M σ + increment M σ false
    · -- the `false` child clips; the `true` child is the raised sibling
      have h1 : ¬(3 ≤ rawValue M σ + increment M σ true) := fun h ↦ huniq ⟨h0, h⟩
      rw [if_pos h0] at hf
      rw [if_neg h1, if_pos (by linarith)] at ht
      rw [hf, ht]; ring
    · rw [if_neg h0] at hf
      by_cases h1 : 3 ≤ rawValue M σ + increment M σ true
      · rw [if_pos h1] at ht
        rw [if_pos (by linarith)] at hf
        rw [hf, ht]; ring
      · rw [if_neg h1] at ht
        rw [if_neg (by linarith : ¬(3 ≤ rawValue M σ - increment M σ false))] at hf
        rw [if_neg (by linarith : ¬(3 ≤ rawValue M σ - increment M σ true))] at ht
        rw [hf, ht]; linarith
  · rw [Bool.not_eq_true] at hph
    rw [if_neg (by simp [hph])] at hf ht
    have huniq := not_both_cross_down M hph
    by_cases h0 : rawValue M σ - increment M σ false ≤ 2
    · have h1 : ¬(rawValue M σ - increment M σ true ≤ 2) := fun h ↦ huniq ⟨h0, h⟩
      rw [if_pos h0] at hf
      rw [if_neg h1, if_pos (by linarith)] at ht
      rw [hf, ht]; ring
    · rw [if_neg h0] at hf
      by_cases h1 : rawValue M σ - increment M σ true ≤ 2
      · rw [if_pos h1] at ht
        rw [if_pos (by linarith)] at hf
        rw [hf, ht]; ring
      · rw [if_neg h1] at ht
        rw [if_neg (by linarith : ¬(rawValue M σ + increment M σ false ≤ 2))] at hf
        rw [if_neg (by linarith : ¬(rawValue M σ + increment M σ true ≤ 2))] at ht
        rw [hf, ht]; linarith

/-! ## The bounds

The witness inequalities become `[1, 4]` in one step, because the savings property says the
source cannot have fallen more than `1` since the witnessed phase switch. This is the only
place the savings property is used, and it is why mere positivity would not suffice. -/

theorem srcCapital_le_of_prefix (M : TreeMartingale) (hsav : M.SavingsProperty)
    {ρ σ : BitString} (h : ρ <+: σ) : srcCapital M ρ ≤ srcCapital M σ + 1 := by
  obtain ⟨τ, rfl⟩ := h
  have hs := hsav ρ τ
  rw [srcCapital, srcCapital]
  exact_mod_cast hs

theorem rawValue_bounds_of_up (M : TreeMartingale) (hsav : M.SavingsProperty) {σ : BitString}
    (h : phase M σ = true) : 1 ≤ rawValue M σ ∧ rawValue M σ < 3 := by
  have hinv := phaseInv M σ
  rw [PhaseInv, if_pos h] at hinv
  obtain ⟨hlt, ρ, hρpre, -, hρineq⟩ := hinv
  refine ⟨?_, hlt⟩
  have := srcCapital_le_of_prefix M hsav hρpre
  linarith

theorem rawValue_bounds_of_down (M : TreeMartingale) (hsav : M.SavingsProperty) {σ : BitString}
    (h : phase M σ = false) : 2 < rawValue M σ ∧ rawValue M σ ≤ 4 := by
  have hinv := phaseInv M σ
  rw [PhaseInv, if_neg (by simp [h])] at hinv
  obtain ⟨hgt, ρ, hρpre, -, hρineq⟩ := hinv
  refine ⟨hgt, ?_⟩
  have := srcCapital_le_of_prefix M hsav hρpre
  linarith

theorem rawValue_mem_Icc (M : TreeMartingale) (hsav : M.SavingsProperty) (σ : BitString) :
    rawValue M σ ∈ Set.Icc (1 : ℚ) 4 := by
  by_cases h : phase M σ = true
  · obtain ⟨h1, h2⟩ := rawValue_bounds_of_up M hsav h
    exact ⟨h1, by linarith⟩
  · rw [Bool.not_eq_true] at h
    obtain ⟨h1, h2⟩ := rawValue_bounds_of_down M hsav h
    exact ⟨by linarith, h2⟩

/-- The sole license needed to convert the signed value back to the nonnegative layer. -/
theorem rawValue_nonneg (M : TreeMartingale) (hsav : M.SavingsProperty) (σ : BitString) :
    0 ≤ rawValue M σ := by
  have := (rawValue_mem_Icc M hsav σ).1
  linarith

/-! ## Phase transitions and constant-phase runs

The step inequalities below say the oscillator does at least as well as the source while the
phase holds. Sibling clipping moves each one in the favorable direction, since the retained
sibling is raised in the up phase and lowered in the down phase. They are stated for any
constant-phase interval — no maximality, and no stored "last switch" data. -/

/-- Crossing up pins the value to exactly `3`. -/
theorem rawValue_eq_three_of_switch (M : TreeMartingale) {σ : BitString} {b : Bool}
    (hσ : phase M σ = true) (hnext : phase M (σ ++ [b]) = false) :
    rawValue M (σ ++ [b]) = 3 := by
  rw [phase_append, if_pos hσ] at hnext
  by_cases h : 3 ≤ rawValue M σ + increment M σ b
  · rw [rawValue_append, if_pos hσ, if_pos h]
  · rw [if_neg h] at hnext; exact absurd hnext (by simp)

/-- Crossing down pins the value to exactly `2`. -/
theorem rawValue_eq_two_of_switch (M : TreeMartingale) {σ : BitString} {b : Bool}
    (hσ : phase M σ = false) (hnext : phase M (σ ++ [b]) = true) :
    rawValue M (σ ++ [b]) = 2 := by
  rw [phase_append, if_neg (by simp [hσ])] at hnext
  by_cases h : rawValue M σ - increment M σ b ≤ 2
  · rw [rawValue_append, if_neg (by simp [hσ]), if_pos h]
  · rw [if_neg h] at hnext; exact absurd hnext (by simp)

/-- While the up phase holds, the oscillator gains at least what the source gains. -/
theorem up_step_le (M : TreeMartingale) {σ : BitString} {b : Bool}
    (hσ : phase M σ = true) (hnext : phase M (σ ++ [b]) = true) :
    rawValue M σ + srcCapital M (σ ++ [b]) ≤ rawValue M (σ ++ [b]) + srcCapital M σ := by
  have hno : ¬(3 ≤ rawValue M σ + increment M σ b) := by
    intro h
    rw [phase_append, if_pos hσ, if_pos h] at hnext
    exact absurd hnext (by simp)
  rw [srcCapital_append, rawValue_append, if_pos hσ, if_neg hno]
  by_cases h2 : 3 ≤ rawValue M σ - increment M σ b
  · rw [if_pos h2]; linarith
  · rw [if_neg h2]; linarith

/-- While the down phase holds, the oscillator loses at most what the source gains. -/
theorem down_step_le (M : TreeMartingale) {σ : BitString} {b : Bool}
    (hσ : phase M σ = false) (hnext : phase M (σ ++ [b]) = false) :
    rawValue M (σ ++ [b]) + srcCapital M (σ ++ [b]) ≤ rawValue M σ + srcCapital M σ := by
  have hno : ¬(rawValue M σ - increment M σ b ≤ 2) := by
    intro h
    rw [phase_append, if_neg (by simp [hσ]), if_pos h] at hnext
    exact absurd hnext (by simp)
  rw [srcCapital_append, rawValue_append, if_neg (by simp [hσ]), if_neg hno]
  by_cases h2 : rawValue M σ + increment M σ b ≤ 2
  · rw [if_pos h2]; linarith
  · rw [if_neg h2]; linarith

/-- Telescoped over a constant up-phase interval. -/
theorem up_run_le (M : TreeMartingale) (x : Cantor) {n m : ℕ} (hnm : n ≤ m)
    (hphase : ∀ k, n ≤ k → k ≤ m → phase M (initSeg x k) = true) :
    rawValue M (initSeg x n) + srcCapital M (initSeg x m)
      ≤ rawValue M (initSeg x m) + srcCapital M (initSeg x n) := by
  induction m, hnm using Nat.le_induction with
  | base => linarith
  | succ m hm ih =>
    have hres : ∀ k, n ≤ k → k ≤ m → phase M (initSeg x k) = true :=
      fun k h1 h2 ↦ hphase k h1 (h2.trans (Nat.le_succ m))
    have hstep := up_step_le M (b := x m) (hphase m hm (Nat.le_succ m))
      (by rw [← initSeg_succ]; exact hphase (m + 1) (hm.trans (Nat.le_succ m)) (le_refl _))
    rw [initSeg_succ] at *
    linarith [ih hres]

/-- Telescoped over a constant down-phase interval. -/
theorem down_run_le (M : TreeMartingale) (x : Cantor) {n m : ℕ} (hnm : n ≤ m)
    (hphase : ∀ k, n ≤ k → k ≤ m → phase M (initSeg x k) = false) :
    rawValue M (initSeg x m) + srcCapital M (initSeg x m)
      ≤ rawValue M (initSeg x n) + srcCapital M (initSeg x n) := by
  induction m, hnm using Nat.le_induction with
  | base => linarith
  | succ m hm ih =>
    have hres : ∀ k, n ≤ k → k ≤ m → phase M (initSeg x k) = false :=
      fun k h1 h2 ↦ hphase k h1 (h2.trans (Nat.le_succ m))
    have hstep := down_step_le M (b := x m) (hphase m hm (Nat.le_succ m))
      (by rw [← initSeg_succ]; exact hphase (m + 1) (hm.trans (Nat.le_succ m)) (le_refl _))
    rw [initSeg_succ] at *
    linarith [ih hres]

/-! ## Oscillation

Success rules out an indefinitely constant phase, because a run inequality bounds the source's
gain over any constant-phase interval while success makes that gain unbounded. Locating an
adjacent phase change then pins the value to `3` or `2` exactly. -/

/-- A Boolean sequence differing at two indices changes somewhere adjacent between them, and the
first such change still agrees with the left endpoint. -/
private theorem exists_adjacent_ne_of_ne (p : ℕ → Bool) {n m : ℕ} (hnm : n ≤ m)
    (hne : p n ≠ p m) : ∃ k, n ≤ k ∧ k < m ∧ p k = p n ∧ p (k + 1) ≠ p n := by
  induction m, hnm using Nat.le_induction with
  | base => exact absurd rfl hne
  | succ m hm ih =>
    by_cases hpm : p n = p m
    · exact ⟨m, hm, Nat.lt_succ_self m, hpm.symm, fun h ↦ hne h.symm⟩
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih hpm
      exact ⟨k, hk1, hk2.trans (Nat.lt_succ_self m), hk3, hk4⟩

/-- Success forces a phase change after any index. A constant-phase run bounds the source's
gain by a run inequality, while success makes that gain exceed the bound. -/
theorem exists_phase_switch (M : TreeMartingale) (hsav : M.SavingsProperty) {x : Cantor}
    (h : M.Succeeds x) (n : ℕ) :
    ∃ k, n ≤ k ∧ phase M (initSeg x k) = phase M (initSeg x n) ∧
      phase M (initSeg x (k + 1)) ≠ phase M (initSeg x n) := by
  obtain ⟨m, hm, hcap⟩ := Filter.frequently_atTop.mp
    (h.frequently_ge (M.capital (initSeg x n) + 4)) n
  have hcapQ : srcCapital M (initSeg x n) + 4 ≤ srcCapital M (initSeg x m) := by
    rw [srcCapital, srcCapital]
    exact_mod_cast hcap
  -- the phase cannot be constant on `[n, m]`: either run inequality caps the gain at `2`
  have hnotconst : ¬∀ k, n ≤ k → k ≤ m → phase M (initSeg x k) = phase M (initSeg x n) := by
    intro hconst
    by_cases hnv : phase M (initSeg x n) = true
    · have hrun := up_run_le M x hm fun k h1 h2 ↦ (hconst k h1 h2).trans hnv
      have h1 := (rawValue_bounds_of_up M hsav hnv).1
      have h2 := (rawValue_bounds_of_up M hsav
        ((hconst m hm (le_refl m)).trans hnv)).2
      linarith
    · rw [Bool.not_eq_true] at hnv
      have hrun := down_run_le M x hm fun k h1 h2 ↦ (hconst k h1 h2).trans hnv
      have h1 := (rawValue_bounds_of_down M hsav
        ((hconst m hm (le_refl m)).trans hnv)).1
      have h2 := (rawValue_bounds_of_down M hsav hnv).2
      linarith
  push Not at hnotconst
  obtain ⟨k, hk1, -, hkne⟩ := hnotconst
  obtain ⟨j, hj1, -, hj3, hj4⟩ :=
    exists_adjacent_ne_of_ne (fun i ↦ phase M (initSeg x i)) hk1 (Ne.symm hkne)
  exact ⟨j, hj1, hj3, hj4⟩

/-- From an up-phase index, the next switch lands on exactly `3`. -/
theorem exists_eq_three_of_up (M : TreeMartingale) (hsav : M.SavingsProperty) {x : Cantor}
    (h : M.Succeeds x) {n : ℕ} (hn : phase M (initSeg x n) = true) :
    ∃ m, n < m ∧ rawValue M (initSeg x m) = 3 := by
  obtain ⟨k, hk, hkeq, hkne⟩ := exists_phase_switch M hsav h n
  have hkt : phase M (initSeg x k) = true := hkeq.trans hn
  have hkf : phase M (initSeg x (k + 1)) = false := by rw [hn] at hkne; simpa using hkne
  refine ⟨k + 1, by omega, ?_⟩
  rw [initSeg_succ]
  exact rawValue_eq_three_of_switch M hkt (by rw [← initSeg_succ]; exact hkf)

/-- From a down-phase index, the next switch lands on exactly `2`. -/
theorem exists_eq_two_of_down (M : TreeMartingale) (hsav : M.SavingsProperty) {x : Cantor}
    (h : M.Succeeds x) {n : ℕ} (hn : phase M (initSeg x n) = false) :
    ∃ m, n < m ∧ rawValue M (initSeg x m) = 2 := by
  obtain ⟨k, hk, hkeq, hkne⟩ := exists_phase_switch M hsav h n
  have hkf : phase M (initSeg x k) = false := hkeq.trans hn
  have hkt : phase M (initSeg x (k + 1)) = true := by rw [hn] at hkne; simpa using hkne
  refine ⟨k + 1, by omega, ?_⟩
  rw [initSeg_succ]
  exact rawValue_eq_two_of_switch M hkf (by rw [← initSeg_succ]; exact hkt)

/-- **The oscillator visits `3` arbitrarily late.** -/
theorem frequently_rawValue_eq_three (M : TreeMartingale) (hsav : M.SavingsProperty)
    {x : Cantor} (h : M.Succeeds x) :
    ∃ᶠ n in Filter.atTop, rawValue M (initSeg x n) = 3 := by
  refine Filter.frequently_atTop.2 fun N ↦ ?_
  by_cases hN : phase M (initSeg x N) = true
  · obtain ⟨m, hm, hval⟩ := exists_eq_three_of_up M hsav h hN
    exact ⟨m, le_of_lt hm, hval⟩
  · rw [Bool.not_eq_true] at hN
    obtain ⟨k, hk, hkeq, hkne⟩ := exists_phase_switch M hsav h N
    have hkt : phase M (initSeg x (k + 1)) = true := by rw [hN] at hkne; simpa using hkne
    obtain ⟨m, hm, hval⟩ := exists_eq_three_of_up M hsav h hkt
    exact ⟨m, by omega, hval⟩

/-- **The oscillator visits `2` arbitrarily late.** -/
theorem frequently_rawValue_eq_two (M : TreeMartingale) (hsav : M.SavingsProperty)
    {x : Cantor} (h : M.Succeeds x) :
    ∃ᶠ n in Filter.atTop, rawValue M (initSeg x n) = 2 := by
  refine Filter.frequently_atTop.2 fun N ↦ ?_
  by_cases hN : phase M (initSeg x N) = true
  · obtain ⟨k, hk, hkeq, hkne⟩ := exists_phase_switch M hsav h N
    have hkf : phase M (initSeg x (k + 1)) = false := by rw [hN] at hkne; simpa using hkne
    obtain ⟨m, hm, hval⟩ := exists_eq_two_of_down M hsav h hkf
    exact ⟨m, by omega, hval⟩
  · rw [Bool.not_eq_true] at hN
    obtain ⟨m, hm, hval⟩ := exists_eq_two_of_down M hsav h hN
    exact ⟨m, le_of_lt hm, hval⟩

/-! ## The coded oscillator

The same recursion on codes, carrying a `RatCode` value and the phase bit. Signed arithmetic is
internal; only the output is converted back, licensed by `rawValue_nonneg`. `PathFuelOk` covers
every source evaluation the fold performs, and the coded rational operations are total, so no
oscillator-specific convergence predicate is needed. -/

open Nat.Partrec (Code)

/-- The coded capital increment at `σ` on bit `b`. -/
def codedIncrement (p : Code) (s : ℕ) (σ : BitString) (b : Bool) : ℕ :=
  RatCode.sub (RatCode.ofNNRat (evalD p s (Encodable.encode (σ ++ [b]))))
    (RatCode.ofNNRat (evalD p s (Encodable.encode σ)))

/-- One coded step, mirroring `oscStep`. -/
def oscCodeStep (p : Code) (s : ℕ) (q : BitString × ℕ × Bool) (b : Bool) : BitString × ℕ × Bool :=
  if q.2.2 then
    if RatCode.le (RatCode.ofNat 3) (RatCode.add q.2.1 (codedIncrement p s q.1 b)) then
      (q.1 ++ [b], RatCode.ofNat 3, false)
    else if RatCode.le (RatCode.ofNat 3) (RatCode.sub q.2.1 (codedIncrement p s q.1 b)) then
      (q.1 ++ [b], RatCode.sub (RatCode.double q.2.1) (RatCode.ofNat 3), true)
    else (q.1 ++ [b], RatCode.add q.2.1 (codedIncrement p s q.1 b), true)
  else
    if RatCode.le (RatCode.sub q.2.1 (codedIncrement p s q.1 b)) (RatCode.ofNat 2) then
      (q.1 ++ [b], RatCode.ofNat 2, true)
    else if RatCode.le (RatCode.add q.2.1 (codedIncrement p s q.1 b)) (RatCode.ofNat 2) then
      (q.1 ++ [b], RatCode.sub (RatCode.double q.2.1) (RatCode.ofNat 2), false)
    else (q.1 ++ [b], RatCode.sub q.2.1 (codedIncrement p s q.1 b), false)

def oscCodePair (p : Code) (s : ℕ) (σ : BitString) : BitString × ℕ × Bool :=
  σ.foldl (oscCodeStep p s) ([], (RatCode.ofNat 2, true))

theorem oscCodeStep_fst (p : Code) (s : ℕ) (q : BitString × ℕ × Bool) (b : Bool) :
    (oscCodeStep p s q b).1 = q.1 ++ [b] := by
  rw [oscCodeStep]
  split
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem foldl_oscCodeStep_fst (p : Code) (s : ℕ) (σ : BitString) :
    ∀ (τ : BitString) (q : ℕ × Bool), (σ.foldl (oscCodeStep p s) (τ, q)).1 = τ ++ σ := by
  induction σ with
  | nil => intro τ q; simp
  | cons b σ ih =>
    intro τ q
    rw [List.foldl_cons, ih, oscCodeStep_fst]
    simp

@[simp] theorem oscCodePair_fst (p : Code) (s : ℕ) (σ : BitString) :
    (oscCodePair p s σ).1 = σ := by
  rw [oscCodePair, foldl_oscCodeStep_fst, List.nil_append]

theorem oscCodePair_append (p : Code) (s : ℕ) (σ : BitString) (b : Bool) :
    oscCodePair p s (σ ++ [b]) = oscCodeStep p s (oscCodePair p s σ) b := by
  rw [oscCodePair, oscCodePair, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The coded increment decodes to the semantic one. -/
theorem value_codedIncrement (M : ComputableMartingale) {s : ℕ} {σ : BitString} {b : Bool}
    (hσ : evalD M.program.program s (Encodable.encode σ)
      = M.program.toFun (Encodable.encode σ))
    (hσb : evalD M.program.program s (Encodable.encode (σ ++ [b]))
      = M.program.toFun (Encodable.encode (σ ++ [b]))) :
    RatCode.value (codedIncrement M.program.program s σ b)
      = increment M.toTreeMartingale σ b := by
  rw [codedIncrement, RatCode.value_sub, RatCode.value_ofNNRat, RatCode.value_ofNNRat,
    hσ, hσb, M.eval_capital, M.eval_capital, increment, srcCapital, srcCapital]

/-- **The acceptance theorem**: the coded fold decodes to the semantic value and phase. Both
components together, so the branch analysis is done once. -/
theorem oscCodePair_value (M : ComputableMartingale) {s : ℕ} {σ : BitString}
    (hfuel : M.program.PathFuelOk s σ) :
    RatCode.value (oscCodePair M.program.program s σ).2.1 = rawValue M.toTreeMartingale σ ∧
      (oscCodePair M.program.program s σ).2.2 = phase M.toTreeMartingale σ := by
  induction σ using List.reverseRecOn with
  | nil =>
    have hv : (oscCodePair M.program.program s []).2.1 = RatCode.ofNat 2 := rfl
    have hp : (oscCodePair M.program.program s []).2.2 = true := rfl
    refine ⟨?_, ?_⟩
    · rw [hv, RatCode.value_ofNat, rawValue_nil]; norm_num
    · rw [hp, phase_nil]
  | append_singleton σ b ih =>
    have hσ : M.program.PathFuelOk s σ :=
      fun τ hτ ↦ hfuel τ (hτ.trans (List.prefix_append σ [b]))
    obtain ⟨ihv, ihp⟩ := ih hσ
    have hev := hfuel σ (List.prefix_append σ [b])
    have hevb := hfuel (σ ++ [b]) (List.prefix_refl _)
    have hinc := value_codedIncrement M hev hevb
    -- the two candidate values decode to the semantic ones
    have hup : RatCode.value (RatCode.add (oscCodePair M.program.program s σ).2.1
        (codedIncrement M.program.program s σ b))
        = rawValue M.toTreeMartingale σ + increment M.toTreeMartingale σ b := by
      rw [RatCode.value_add, ihv, hinc]
    have hdn : RatCode.value (RatCode.sub (oscCodePair M.program.program s σ).2.1
        (codedIncrement M.program.program s σ b))
        = rawValue M.toTreeMartingale σ - increment M.toTreeMartingale σ b := by
      rw [RatCode.value_sub, ihv, hinc]
    have h2v : ∀ c : ℕ, RatCode.value (RatCode.sub
        (RatCode.double (oscCodePair M.program.program s σ).2.1) (RatCode.ofNat c))
        = 2 * rawValue M.toTreeMartingale σ - (c : ℚ) := by
      intro c
      rw [RatCode.value_sub, RatCode.value_double, RatCode.value_ofNat, ihv]
    rw [oscCodePair_append, oscCodeStep, oscCodePair_fst, rawValue_append, phase_append, ihp]
    by_cases hph : phase M.toTreeMartingale σ = true
    · rw [if_pos hph, if_pos hph, if_pos hph]
      by_cases h1 : (3 : ℚ) ≤ rawValue M.toTreeMartingale σ + increment M.toTreeMartingale σ b
      · rw [if_pos (by rw [RatCode.le_iff, RatCode.value_ofNat, hup]; exact_mod_cast h1),
          if_pos h1, if_pos h1]
        exact ⟨by rw [RatCode.value_ofNat]; norm_num, rfl⟩
      · rw [if_neg (by rw [Bool.not_eq_true, Bool.eq_false_iff, ne_eq, RatCode.le_iff,
              RatCode.value_ofNat, hup]; exact_mod_cast h1),
          if_neg h1, if_neg h1]
        by_cases h2 : (3 : ℚ) ≤ rawValue M.toTreeMartingale σ - increment M.toTreeMartingale σ b
        · rw [if_pos (by rw [RatCode.le_iff, RatCode.value_ofNat, hdn]; exact_mod_cast h2),
            if_pos h2]
          exact ⟨by rw [h2v]; norm_num, rfl⟩
        · rw [if_neg (by rw [Bool.not_eq_true, Bool.eq_false_iff, ne_eq, RatCode.le_iff,
                RatCode.value_ofNat, hdn]; exact_mod_cast h2), if_neg h2]
          exact ⟨hup, rfl⟩
    · rw [Bool.not_eq_true] at hph
      have hnot : ¬(phase M.toTreeMartingale σ = true) := by simp [hph]
      rw [if_neg hnot, if_neg hnot, if_neg hnot]
      by_cases h1 : rawValue M.toTreeMartingale σ - increment M.toTreeMartingale σ b ≤ (2 : ℚ)
      · rw [if_pos (by rw [RatCode.le_iff, RatCode.value_ofNat, hdn]; exact_mod_cast h1),
          if_pos h1, if_pos h1]
        exact ⟨by rw [RatCode.value_ofNat]; norm_num, rfl⟩
      · rw [if_neg (by rw [Bool.not_eq_true, Bool.eq_false_iff, ne_eq, RatCode.le_iff,
              RatCode.value_ofNat, hdn]; exact_mod_cast h1),
          if_neg h1, if_neg h1]
        by_cases h2 : rawValue M.toTreeMartingale σ + increment M.toTreeMartingale σ b ≤ (2 : ℚ)
        · rw [if_pos (by rw [RatCode.le_iff, RatCode.value_ofNat, hup]; exact_mod_cast h2),
            if_pos h2]
          exact ⟨by rw [h2v]; norm_num, rfl⟩
        · rw [if_neg (by rw [Bool.not_eq_true, Bool.eq_false_iff, ne_eq, RatCode.le_iff,
                RatCode.value_ofNat, hup]; exact_mod_cast h2), if_neg h2]
          exact ⟨hdn, rfl⟩

/-! ## The packaged oscillator

The semantic capital is built directly from `rawValue`, so the coding representation stays
behind `eval_capital` and later slope arguments never see it. -/

/-- The oscillator's capital: the raw value, known nonnegative. -/
def oscillatorCapital (M : SavingsComputableMartingale) (σ : BitString) : ℚ≥0 :=
  ⟨rawValue M.toTreeMartingale σ, rawValue_nonneg M.toTreeMartingale M.savingsProperty σ⟩

@[simp, norm_cast] theorem coe_oscillatorCapital (M : SavingsComputableMartingale)
    (σ : BitString) : ((oscillatorCapital M σ : ℚ≥0) : ℚ) = rawValue M.toTreeMartingale σ := rfl

theorem oscillatorCapital_fair (M : SavingsComputableMartingale) (σ : BitString) :
    oscillatorCapital M (σ ++ [false]) + oscillatorCapital M (σ ++ [true])
      = 2 * oscillatorCapital M σ := by
  have h := rawValue_fair M.toTreeMartingale σ
  rw [← NNRat.coe_inj]
  push_cast [coe_oscillatorCapital]
  exact h

/-- The semantic oscillating martingale. -/
def oscillatorTree (M : SavingsComputableMartingale) : TreeMartingale where
  capital := oscillatorCapital M
  fair := oscillatorCapital_fair M

/-! ## The program -/

-- The coded arithmetic unfolds into `Nat.unpair` and hence `Nat.sqrt`, which makes elaboration
-- explode during `Primrec` composition.
attribute [local irreducible] RatCode.add RatCode.sub RatCode.double RatCode.ofNat
  RatCode.ofNNRat RatCode.le RatCode.toNNRat

private theorem primrec_codedIncrement :
    Primrec fun z : ((Code × ℕ) × BitString) × Bool ↦
      codedIncrement z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have harg : ∀ c : Bool, Primrec fun v : ((Code × ℕ) × BitString) × Bool ↦
      evalD v.1.1.1 v.1.1.2 (Encodable.encode (v.1.2 ++ [c])) := fun c ↦
    primrec_evalD.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.encode.comp (Primrec.list_append.comp
          (Primrec.snd.comp Primrec.fst) (Primrec.const [c]))))
  have hbit : Primrec fun v : ((Code × ℕ) × BitString) × Bool ↦
      evalD v.1.1.1 v.1.1.2 (Encodable.encode (v.1.2 ++ [v.2])) :=
    primrec_evalD.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.encode.comp (Primrec.list_append.comp
          (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))))
  have hpar : Primrec fun v : ((Code × ℕ) × BitString) × Bool ↦
      evalD v.1.1.1 v.1.1.2 (Encodable.encode v.1.2) :=
    primrec_evalD.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.encode.comp (Primrec.snd.comp Primrec.fst)))
  exact RatCode.primrec_sub.comp (RatCode.primrec_ofNNRat.comp hbit)
    (RatCode.primrec_ofNNRat.comp hpar)

private theorem primrec_oscCodePair :
    Primrec fun z : (Code × ℕ) × BitString ↦ oscCodePair z.1.1 z.1.2 z.2 := by
  have hstep : Primrec₂ fun (z : (Code × ℕ) × BitString) (q : (BitString × ℕ × Bool) × Bool) ↦
      oscCodeStep z.1.1 z.1.2 q.1 q.2 := by
    unfold oscCodeStep
    have hpref : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × Bool) × Bool) ↦
        v.2.1.1 ++ [v.2.2] :=
      Primrec.list_append.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    have hval : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × Bool) × Bool) ↦
        v.2.1.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    have hinc : Primrec fun v : ((Code × ℕ) × BitString) × ((BitString × ℕ × Bool) × Bool) ↦
        codedIncrement v.1.1.1 v.1.1.2 v.2.1.1 v.2.2 :=
      primrec_codedIncrement.comp
        ((((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).pair
          (Primrec.snd.comp Primrec.snd))
    have hadd := RatCode.primrec_add.comp hval hinc
    have hsub := RatCode.primrec_sub.comp hval hinc
    have hdbl3 := RatCode.primrec_sub.comp (RatCode.primrec_double.comp hval)
      (Primrec.const (RatCode.ofNat 3))
    have hdbl2 := RatCode.primrec_sub.comp (RatCode.primrec_double.comp hval)
      (Primrec.const (RatCode.ofNat 2))
    refine Primrec.ite (Primrec.eq.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.const true))
      ?_ ?_
    · refine Primrec.ite (Primrec.eq.comp
        (RatCode.primrec_le.comp (Primrec.const (RatCode.ofNat 3)) hadd) (Primrec.const true))
        (Primrec₂.pair.comp hpref (Primrec₂.pair.comp (Primrec.const (RatCode.ofNat 3))
          (Primrec.const false))) ?_
      refine Primrec.ite (Primrec.eq.comp
        (RatCode.primrec_le.comp (Primrec.const (RatCode.ofNat 3)) hsub) (Primrec.const true))
        (Primrec₂.pair.comp hpref (Primrec₂.pair.comp hdbl3 (Primrec.const true)))
        (Primrec₂.pair.comp hpref (Primrec₂.pair.comp hadd (Primrec.const true)))
    · refine Primrec.ite (Primrec.eq.comp
        (RatCode.primrec_le.comp hsub (Primrec.const (RatCode.ofNat 2))) (Primrec.const true))
        (Primrec₂.pair.comp hpref (Primrec₂.pair.comp (Primrec.const (RatCode.ofNat 2))
          (Primrec.const true))) ?_
      refine Primrec.ite (Primrec.eq.comp
        (RatCode.primrec_le.comp hadd (Primrec.const (RatCode.ofNat 2))) (Primrec.const true))
        (Primrec₂.pair.comp hpref (Primrec₂.pair.comp hdbl2 (Primrec.const false)))
        (Primrec₂.pair.comp hpref (Primrec₂.pair.comp hsub (Primrec.const false)))
  unfold oscCodePair
  refine Primrec.list_foldl Primrec.snd ?_ hstep
  exact Primrec₂.pair.comp (Primrec.const [])
    (Primrec₂.pair.comp (Primrec.const (RatCode.ofNat 2)) (Primrec.const true))

/-- On input `encode σ`, the coded capital of the oscillator at `σ`. -/
def oscillatorEnum (p : Code) : ℕ →. ℕ := fun input ↦
  (Nat.rfind fun s ↦ Part.some
      (pathFuelOk p s ((Encodable.decode input : Option BitString).getD []))).map
    fun s ↦ RatCode.toNNRat
      (oscCodePair p s ((Encodable.decode input : Option BitString).getD [])).2.1

/-- Uniform in the raw source program. -/
theorem partrec_oscillatorEnumUniform :
    Partrec fun z : Code × ℕ ↦ oscillatorEnum z.1 z.2 := by
  have hstr : Primrec fun z : Code × ℕ ↦ (Encodable.decode z.2 : Option BitString).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const [])
  have harg : Primrec fun q : (Code × ℕ) × ℕ ↦
      (((q.1.1, q.2), (Encodable.decode q.1.2 : Option BitString).getD [])
        : (Code × ℕ) × BitString) :=
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair (hstr.comp Primrec.fst)
  exact Partrec.map
    (Partrec.rfind (Computable₂.partrec₂ (primrec_pathFuelOk.comp harg).to_comp.to₂))
    ((RatCode.primrec_toNNRat.comp
      (Primrec.fst.comp (Primrec.snd.comp (primrec_oscCodePair.comp harg)))).to_comp.to₂)

theorem partrec_oscillatorEnum (p : Code) : Nat.Partrec (oscillatorEnum p) :=
  Partrec.nat_iff.mp ((partrec_oscillatorEnumUniform.comp
    (Computable.pair (Computable.const p) Computable.id)).of_eq fun _ ↦ rfl)

namespace SavingsComputableMartingale

variable (M : SavingsComputableMartingale)

theorem oscillatorEnum_dom (input : ℕ) :
    (oscillatorEnum M.program.program input).Dom := by
  obtain ⟨s, hs⟩ :=
    exists_pathFuelOk M.program ((Encodable.decode input : Option BitString).getD [])
  obtain ⟨t, htmem, -⟩ := Nat.rfind_min'
    (p := fun s ↦ pathFuelOk M.program.program s
      ((Encodable.decode input : Option BitString).getD [])) (m := s) hs
  exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ htmem⟩

/-- The program computing the oscillator's capital. -/
noncomputable def oscillatorCode : NatFunctionCode :=
  NatFunctionCode.ofPartrecTotal (partrec_oscillatorEnum M.program.program) M.oscillatorEnum_dom

theorem oscillatorCode_value (σ : BitString) :
    NNRatCode.value (M.oscillatorCode.toFun (Encodable.encode σ)) = oscillatorCapital M σ := by
  have hmem : M.oscillatorCode.toFun (Encodable.encode σ)
      ∈ oscillatorEnum M.program.program (Encodable.encode σ) := by
    rw [oscillatorCode, NatFunctionCode.ofPartrecTotal_toFun]
    exact Part.get_mem _
  rw [oscillatorEnum, Encodable.encodek, Option.getD_some, Part.mem_map_iff] at hmem
  obtain ⟨s, hs, hval⟩ := hmem
  have hok : pathFuelOk M.program.program s σ = true := by
    have := Nat.rfind_spec hs; simpa using this
  obtain ⟨hv, -⟩ := oscCodePair_value M.toComputableMartingale (pathFuelOk_spec hok)
  rw [← NNRat.coe_inj, coe_oscillatorCapital, ← hval,
    RatCode.value_toNNRat (by rw [hv]; exact rawValue_nonneg _ M.savingsProperty σ), hv]

/-- **The bounded oscillating martingale of a source with the savings property.** -/
noncomputable def oscillator : ComputableMartingale where
  toTreeMartingale := oscillatorTree M
  program := M.oscillatorCode
  eval_capital := M.oscillatorCode_value

@[simp] theorem oscillator_capital (σ : BitString) :
    M.oscillator.capital σ = oscillatorCapital M σ := rfl

theorem oscillator_bounds (σ : BitString) :
    1 ≤ M.oscillator.capital σ ∧ M.oscillator.capital σ ≤ 4 := by
  have h := rawValue_mem_Icc M.toTreeMartingale M.savingsProperty σ
  rw [oscillator_capital]
  constructor
  · rw [← NNRat.coe_le_coe]; exact_mod_cast h.1
  · rw [← NNRat.coe_le_coe]; exact_mod_cast h.2

variable {M}

/-- The oscillator reaches exactly `3` arbitrarily late along any path where the source
succeeds. -/
theorem frequently_oscillator_capital_eq_three {x : Cantor}
    (h : M.toTreeMartingale.Succeeds x) :
    ∃ᶠ n in Filter.atTop, M.oscillator.capital (initSeg x n) = 3 := by
  refine (frequently_rawValue_eq_three M.toTreeMartingale M.savingsProperty h).mono fun n hn ↦ ?_
  rw [oscillator_capital, ← NNRat.coe_inj, coe_oscillatorCapital, hn]
  norm_num

/-- And exactly `2` arbitrarily late. -/
theorem frequently_oscillator_capital_eq_two {x : Cantor}
    (h : M.toTreeMartingale.Succeeds x) :
    ∃ᶠ n in Filter.atTop, M.oscillator.capital (initSeg x n) = 2 := by
  refine (frequently_rawValue_eq_two M.toTreeMartingale M.savingsProperty h).mono fun n hn ↦ ?_
  rw [oscillator_capital, ← NNRat.coe_inj, coe_oscillatorCapital, hn]
  norm_num

end SavingsComputableMartingale

end AlgorithmicRandomness
