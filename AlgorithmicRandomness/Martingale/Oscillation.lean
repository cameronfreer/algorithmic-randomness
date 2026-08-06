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

end AlgorithmicRandomness
