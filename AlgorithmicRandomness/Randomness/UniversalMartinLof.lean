/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.EffectiveOpen.Trim
import AlgorithmicRandomness.Randomness.MartinLof

/-!
# The universal Martin-Löf test

A single program `universalCode` whose `n`-th open set absorbs, with a shift, every Martin-Löf
test. On input `⟨n, ⟨e, j⟩⟩` it runs the trimmed enumeration of the `e`-th program at offset
`e + 1`: candidate `e` therefore contributes `e`'s level `n + e + 1`, forced by trimming to
weigh at most `2⁻⁽ⁿ⁺ᵉ⁺¹⁾`, so the levels sum geometrically to `2⁻ⁿ`.

The universal test is a genuine coded object, not a semantic union over indices:
`denote_universalOpen` is a *derived* description of one code's denotation.

Trimming makes every candidate a legal contribution whether or not its program was a test to
begin with, while `denote_trim_of_le` leaves a genuine test untouched at its own index — which
is exactly the absorption step.

The consequences are the one-test characterization `isMartinLofRandom_iff_not_captures_universal`
and conullity: `fairCoin {x | IsMartinLofRandom x} = 1`, i.e. `ae_isMartinLofRandom`.
-/

open Nat.Partrec (Code)
open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## The universal program -/

/-- Candidate `e`: the `e`-th program, trimmed at offset `e + 1`. Level `n` of this family is
the `e`-th program's level `n + e + 1`, forced to weigh at most `2⁻⁽ⁿ⁺ᵉ⁺¹⁾`. -/
noncomputable def candidate (e : ℕ) : UniformOpenCode :=
  (UniformOpenCode.mk (Denumerable.ofNat Code e)).trim (e + 1)

theorem candidate_program (e : ℕ) :
    (candidate e).program = trimCode (Denumerable.ofNat Code e) (e + 1) := rfl

/-- On input `⟨n, ⟨e, j⟩⟩`, run candidate `e`'s trimmed enumeration at level `n` on input `j`. -/
def universalEnum : ℕ →. ℕ := fun input ↦
  trimEnumUniform ((Denumerable.ofNat Code input.unpair.2.unpair.1,
    input.unpair.2.unpair.1 + 1), Nat.pair input.unpair.1 input.unpair.2.unpair.2)

theorem partrec_universalEnum' : Partrec universalEnum := by
  have he : Computable fun input : ℕ ↦ input.unpair.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hj : Computable fun input : ℕ ↦ input.unpair.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hn : Computable fun input : ℕ ↦ input.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
  exact partrec_trimEnumUniform.comp
    (Computable.pair
      (Computable.pair ((Primrec.ofNat Code).to_comp.comp he) (Computable.succ.comp he))
      (Computable₂.comp Primrec₂.natPair.to_comp.to₂ hn hj))

theorem partrec_universalEnum : Nat.Partrec universalEnum :=
  Partrec.nat_iff.mp partrec_universalEnum'

/-- The universal test's code: one program, obtained from the uniform computability theorem. -/
noncomputable def universalCode : Code := (Code.exists_code.mp partrec_universalEnum).choose

theorem eval_universalCode : universalCode.eval = universalEnum :=
  (Code.exists_code.mp partrec_universalEnum).choose_spec

noncomputable def universalOpen : UniformOpenCode := ⟨universalCode⟩

/-! ## The semantic union -/

theorem enumeratesString_universalCode {n : ℕ} {σ : BitString} :
    EnumeratesString universalCode n σ ↔ ∃ e, EnumeratesString (candidate e).program n σ := by
  constructor
  · rintro ⟨k, m, hm, hdec⟩
    rw [eval_universalCode, universalEnum] at hm
    simp only [Nat.unpair_pair] at hm
    refine ⟨k.unpair.1, k.unpair.2, m, ?_, hdec⟩
    rwa [candidate_program, eval_trimCode]
  · rintro ⟨e, j, m, hm, hdec⟩
    rw [candidate_program, eval_trimCode] at hm
    refine ⟨Nat.pair e j, m, ?_, hdec⟩
    rw [eval_universalCode, universalEnum]
    simpa [trimEnumUniform] using hm

/-- The `n`-th universal level is the union of the trimmed candidate levels. This is a derived
description of a single code's denotation, not the definition. -/
theorem denote_universalOpen (n : ℕ) :
    universalOpen.denote n = ⋃ e, (candidate e).denote n := by
  ext x
  rw [UniformOpenCode.mem_denote_iff_enumerates, Set.mem_iUnion]
  simp only [UniformOpenCode.mem_denote_iff_enumerates]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨e, he⟩ := enumeratesString_universalCode.mp hσ
    exact ⟨e, σ, he, hx⟩
  · rintro ⟨e, σ, he, hx⟩
    exact ⟨σ, enumeratesString_universalCode.mpr ⟨e, he⟩, hx⟩

/-! ## The geometric budget -/

private theorem tsum_pow_inv_two_shift (n : ℕ) :
    ∑' e : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + e + 1) = (2⁻¹ : ℝ≥0∞) ^ n := by
  have h : ∀ e : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + e + 1) = 2⁻¹ ^ n * 2⁻¹ ^ (e + 1) := by
    intro e
    rw [← pow_add, Nat.add_assoc]
  have hgeom : (2⁻¹ : ℝ≥0∞) * (1 - 2⁻¹)⁻¹ = 1 := by
    rw [ENNReal.one_sub_inv_two, inv_inv, ENNReal.inv_mul_cancel (by simp) (by simp)]
  rw [tsum_congr h, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, hgeom, mul_one]

theorem fairCoin_denote_universalOpen_le (n : ℕ) :
    fairCoin (universalOpen.denote n) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  have hcand : ∀ e : ℕ,
      fairCoin ((candidate e).denote n) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + e + 1) := fun e ↦
    UniformOpenCode.fairCoin_denote_trim_le _ (e + 1) n
  rw [denote_universalOpen]
  calc fairCoin (⋃ e, (candidate e).denote n)
      ≤ ∑' e, fairCoin ((candidate e).denote n) := measure_iUnion_le _
    _ ≤ ∑' e : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + e + 1) := ENNReal.tsum_le_tsum hcand
    _ = (2⁻¹ : ℝ≥0∞) ^ n := tsum_pow_inv_two_shift n

/-- The universal Martin-Löf test. -/
noncomputable def universalTest : MartinLofTest where
  openCode := universalOpen
  measure_le := fairCoin_denote_universalOpen_le

@[simp]
theorem universalTest_openCode : universalTest.openCode = universalOpen := rfl

/-! ## Absorption -/

/-- Every Martin-Löf test is absorbed by the universal test, after a shift. -/
theorem exists_offset_subset_universal (T : MartinLofTest) :
    ∃ c : ℕ, ∀ n, T.openCode.denote (n + c) ⊆ universalTest.openCode.denote n := by
  set e := Encodable.encode T.openCode.program with he
  refine ⟨e + 1, fun n ↦ ?_⟩
  have hcode : (UniformOpenCode.mk (Denumerable.ofNat Code e)) = T.openCode := by
    rw [he, Denumerable.ofNat_encode]
  have hcand : (candidate e).denote n = T.openCode.denote (n + (e + 1)) := by
    rw [candidate, hcode]
    exact UniformOpenCode.denote_trim_of_le T.openCode (e + 1) n (T.measure_le (n + (e + 1)))
  rw [universalTest_openCode, denote_universalOpen, ← hcand]
  exact Set.subset_iUnion (fun e ↦ (candidate e).denote n) e

theorem captures_universal_of_captures {T : MartinLofTest} {x : Cantor}
    (h : T.Captures x) : universalTest.Captures x := by
  obtain ⟨c, hc⟩ := exists_offset_subset_universal T
  exact fun n ↦ hc n (h (n + c))

/-! ## The one-test characterization and conullity -/

theorem isMartinLofRandom_iff_not_captures_universal {x : Cantor} :
    IsMartinLofRandom x ↔ ¬universalTest.Captures x := by
  constructor
  · exact fun h ↦ h universalTest
  · exact fun h T hT ↦ h (captures_universal_of_captures hT)

theorem setOf_isMartinLofRandom_eq_compl :
    {x : Cantor | IsMartinLofRandom x} = universalTest.captureSetᶜ := by
  ext x
  rw [Set.mem_compl_iff, Set.mem_setOf_eq, MartinLofTest.mem_captureSet,
    isMartinLofRandom_iff_not_captures_universal]

theorem measurableSet_setOf_isMartinLofRandom :
    MeasurableSet {x : Cantor | IsMartinLofRandom x} := by
  rw [setOf_isMartinLofRandom_eq_compl]
  exact (universalTest.measurableSet_captureSet).compl

/-- Almost every point of Cantor space is Martin-Löf random. -/
theorem fairCoin_setOf_isMartinLofRandom : fairCoin {x : Cantor | IsMartinLofRandom x} = 1 := by
  rw [setOf_isMartinLofRandom_eq_compl,
    measure_compl universalTest.measurableSet_captureSet
      (by rw [universalTest.fairCoin_captureSet]; simp),
    universalTest.fairCoin_captureSet, measure_univ, tsub_zero]

theorem ae_isMartinLofRandom : ∀ᵐ x ∂fairCoin, IsMartinLofRandom x := by
  rw [ae_iff]
  have h : {x : Cantor | ¬IsMartinLofRandom x} = universalTest.captureSet := by
    ext x
    rw [Set.mem_setOf_eq, MartinLofTest.mem_captureSet,
      isMartinLofRandom_iff_not_captures_universal, Classical.not_not]
  rw [h, universalTest.fairCoin_captureSet]

end AlgorithmicRandomness
