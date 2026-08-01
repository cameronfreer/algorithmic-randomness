/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Martingale.Computable
import AlgorithmicRandomness.Randomness.MartinLof

/-!
# Martin-Löf randomness implies computable randomness

Given a computable martingale succeeding on `x`, we build a Martin-Löf test capturing `x`:
level `n` is the set of points along which the capital reaches `2 ^ (n + c)`, where `c` is an
offset with `capital [] ≤ 2 ^ c`. Ville's inequality gives the measure bound
`2 ^ c / 2 ^ (n + c) = 2⁻ⁿ`.

This is the direct stress test of the coded rational representation: the level-`n` open set is
enumerated by a genuine program that runs the martingale's own program and compares its raw
output against a coded threshold with `NNRatCode.le`. Divergence is used only to *reject* — the
martingale's program is total, so no dovetailing is needed.
-/

open Nat.Partrec (Code)
open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## Canonical codes for strings -/

/-- Round a natural to the code of the string it denotes; undecodable naturals fold to `[]`.
Needed because `Encodable.decode` is only a left inverse: without canonicalization a natural
`k ≠ Encodable.encode σ` that happens to decode to `σ` would enumerate `σ` while the capital
was tested at `k`. -/
def canon (k : ℕ) : ℕ := Encodable.encode ((Encodable.decode k : Option BitString).getD [])

theorem primrec_canon : Primrec canon :=
  Primrec.encode.comp (Primrec.option_getD.comp Primrec.decode (Primrec.const []))

theorem computable_canon : Computable canon := primrec_canon.to_comp

@[simp] theorem decode_canon (k : ℕ) :
    (Encodable.decode (canon k) : Option BitString)
      = some ((Encodable.decode k : Option BitString).getD []) := by
  rw [canon, Encodable.encodek]

@[simp] theorem canon_encode (σ : BitString) : canon (Encodable.encode σ) = Encodable.encode σ := by
  rw [canon, Encodable.encodek, Option.getD_some]

@[simp] theorem canon_idem (k : ℕ) : canon (canon k) = canon k := by
  rw [canon, decode_canon, Option.getD_some, ← canon]

/-! ## The threshold enumerator -/

/-- On paired input `⟨n, k⟩`, run the martingale's program on the canonical code of `k` and emit
that code exactly when the capital clears `2 ^ (n + c)`. The `rfind` on a constant predicate is
the filter-or-diverge idiom: it returns `0` when the test holds and diverges otherwise. -/
def thresholdEnum (dprog : Code) (c : ℕ) : ℕ →. ℕ := fun input ↦
  (dprog.eval (canon input.unpair.2)).bind fun v ↦
    (Nat.rfind fun _ ↦ Part.some
        (NNRatCode.le (Nat.pair (2 ^ (input.unpair.1 + c)) 0) v)).map
      fun _ ↦ canon input.unpair.2

theorem partrec_thresholdEnumUniform :
    Partrec fun z : (Code × ℕ) × ℕ ↦ thresholdEnum z.1.1 z.1.2 z.2 := by
  have hcanon : Primrec fun z : (Code × ℕ) × ℕ ↦ canon z.2.unpair.2 :=
    primrec_canon.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have heval : Partrec fun z : (Code × ℕ) × ℕ ↦ (z.1.1).eval (canon z.2.unpair.2) :=
    Code.eval_part.comp (Computable.fst.comp Computable.fst) hcanon.to_comp
  refine Partrec.bind heval ?_
  have hthr : Primrec fun q : ((Code × ℕ) × ℕ) × ℕ ↦
      Nat.pair (2 ^ (q.1.2.unpair.1 + q.1.1.2)) 0 := by
    refine Primrec₂.natPair.comp ?_ (Primrec.const 0)
    refine (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) ?_
    exact Primrec.nat_add.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have htest : Computable fun q : ((Code × ℕ) × ℕ) × ℕ ↦
      NNRatCode.le (Nat.pair (2 ^ (q.1.2.unpair.1 + q.1.1.2)) 0) q.2 :=
    (NNRatCode.primrec_le.comp hthr Primrec.snd).to_comp
  have hout : Computable fun q : ((Code × ℕ) × ℕ) × ℕ ↦ canon q.1.2.unpair.2 :=
    (hcanon.comp Primrec.fst).to_comp
  exact Partrec.map (Partrec.rfind (Computable₂.partrec₂ (htest.comp Computable.fst).to₂))
    (hout.comp Computable.fst).to₂

theorem partrec_thresholdEnum (dprog : Code) (c : ℕ) : Nat.Partrec (thresholdEnum dprog c) :=
  Partrec.nat_iff.mp ((partrec_thresholdEnumUniform.comp
    (Computable.pair (Computable.const (dprog, c)) Computable.id)).of_eq fun _ ↦ rfl)

/-- The code enumerating the strings whose capital clears the threshold. -/
noncomputable def thresholdCode (dprog : Code) (c : ℕ) : Code :=
  (Code.exists_code.mp (partrec_thresholdEnum dprog c)).choose

theorem eval_thresholdCode (dprog : Code) (c : ℕ) :
    (thresholdCode dprog c).eval = thresholdEnum dprog c :=
  (Code.exists_code.mp (partrec_thresholdEnum dprog c)).choose_spec

/-! ## The Ville test of a computable martingale -/

namespace ComputableMartingale

variable (d : ComputableMartingale)

/-- An offset with `capital [] ≤ 2 ^ offset`, by the Archimedean property. -/
noncomputable def offset : ℕ :=
  (pow_unbounded_of_one_lt (R := ℚ≥0) (d.capital []) (by norm_num : (1 : ℚ≥0) < 2)).choose

theorem capital_nil_lt_two_pow : d.capital [] < (2 : ℚ≥0) ^ d.offset :=
  (pow_unbounded_of_one_lt (R := ℚ≥0) (d.capital []) (by norm_num : (1 : ℚ≥0) < 2)).choose_spec

theorem capital_nil_le_two_pow : d.capital [] ≤ (2 : ℚ≥0) ^ d.offset :=
  d.capital_nil_lt_two_pow.le

/-- The coded family whose level `n` is the set of points reaching capital `2 ^ (n + offset)`. -/
noncomputable def thresholdOpen : UniformOpenCode :=
  ⟨thresholdCode d.program.program d.offset⟩

variable {d}

theorem enumeratesString_thresholdCode {n : ℕ} {σ : BitString} :
    EnumeratesString (thresholdCode d.program.program d.offset) n σ
      ↔ (2 : ℚ≥0) ^ (n + d.offset) ≤ d.capital σ := by
  constructor
  · rintro ⟨k, m, hm, hdec⟩
    rw [eval_thresholdCode, thresholdEnum] at hm
    simp only [Nat.unpair_pair] at hm
    rw [Part.mem_bind_iff] at hm
    obtain ⟨v, hv, hmap⟩ := hm
    rw [Part.mem_map_iff] at hmap
    obtain ⟨s, hs, rfl⟩ := hmap
    have hveq : v = d.program.toFun (canon k) := by
      rw [d.program.eval_program (canon k)] at hv
      exact Part.mem_some_iff.mp hv
    have htest : NNRatCode.le (Nat.pair (2 ^ (n + d.offset)) 0) v = true := by
      have := Nat.rfind_spec hs; simpa using this
    rw [decode_canon] at hdec
    have hσ : (Encodable.decode k : Option BitString).getD [] = σ := Option.some_injective _ hdec
    have hcap : NNRatCode.value (d.program.toFun (canon k)) = d.capital σ := by
      simp only [canon, hσ]
      exact d.eval_capital σ
    have hle := (NNRatCode.le_iff _ _).mp (hveq ▸ htest)
    rw [NNRatCode.value_pair_zero, hcap] at hle
    exact_mod_cast hle
  · intro hσ
    refine ⟨Encodable.encode σ, Encodable.encode σ, ?_, Encodable.encodek σ⟩
    rw [eval_thresholdCode, thresholdEnum]
    simp only [Nat.unpair_pair, canon_encode]
    rw [Part.mem_bind_iff]
    have hmemv : d.program.toFun (Encodable.encode σ)
        ∈ d.program.program.eval (Encodable.encode σ) := by
      rw [d.program.eval_program]; exact Part.mem_some _
    refine ⟨d.program.toFun (Encodable.encode σ), hmemv, ?_⟩
    rw [Part.mem_map_iff]
    refine ⟨0, ?_, rfl⟩
    rw [Nat.mem_rfind]
    refine ⟨?_, fun {m} hm ↦ absurd hm (Nat.not_lt_zero m)⟩
    rw [Part.mem_some_iff]
    have hle : NNRatCode.value (Nat.pair (2 ^ (n + d.offset)) 0)
        ≤ NNRatCode.value (d.program.toFun (Encodable.encode σ)) := by
      rw [NNRatCode.value_pair_zero, d.eval_capital]
      exact_mod_cast hσ
    exact ((NNRatCode.le_iff _ _).mpr hle).symm

variable (d)

theorem denote_thresholdOpen (n : ℕ) :
    d.thresholdOpen.denote n = d.reaches ((2 : ℚ≥0) ^ (n + d.offset)) := by
  ext x
  rw [UniformOpenCode.mem_denote_iff_enumerates, TreeMartingale.mem_reaches_iff]
  exact exists_congr fun σ ↦ and_congr_left' enumeratesString_thresholdCode

/-! ## The Ville test and the implication -/

private theorem two_pow_div (n c : ℕ) : (2 : ℝ≥0∞) ^ c / 2 ^ (n + c) = (2⁻¹ : ℝ≥0∞) ^ n := by
  have h1 : (2 : ℝ≥0∞) ^ c ≠ 0 := by simp
  have h2 : (2 : ℝ≥0∞) ^ c ≠ ⊤ := by simp
  rw [pow_add, mul_comm ((2 : ℝ≥0∞) ^ n) (2 ^ c), ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl h1) (Or.inl h2), mul_right_comm, ENNReal.inv_mul_cancel h1 h2,
    one_mul, ← ENNReal.inv_pow]

/-- The Martin-Löf test built from a computable martingale by Ville's inequality. -/
noncomputable def villeTest : MartinLofTest where
  openCode := d.thresholdOpen
  measure_le n := by
    rw [d.denote_thresholdOpen n]
    refine le_trans (TreeMartingale.fairCoin_reaches_le d.toTreeMartingale (by positivity)) ?_
    have hcast : (((2 : ℚ≥0) ^ (n + d.offset) : ℚ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (n + d.offset) := by
      rw [← ENNReal.coe_nnratCast]; push_cast; rfl
    have hnum : ((d.capital [] : ℚ≥0) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ d.offset := by
      rw [show (2 : ℝ≥0∞) ^ d.offset = (((2 : ℚ≥0) ^ d.offset : ℚ≥0) : ℝ≥0∞) by
        rw [← ENNReal.coe_nnratCast]; push_cast; rfl]
      exact coe_nnrat_le_coe.mpr d.capital_nil_le_two_pow
    rw [hcast]
    exact le_trans (ENNReal.div_le_div_right hnum _) (le_of_eq (two_pow_div n d.offset))

@[simp] theorem villeTest_openCode : d.villeTest.openCode = d.thresholdOpen := rfl

variable {d}

/-- A martingale that succeeds is captured by its own Ville test. -/
theorem captures_villeTest_of_succeeds {x : Cantor} (h : d.Succeeds x) :
    d.villeTest.Captures x := fun n ↦ by
  rw [villeTest_openCode, d.denote_thresholdOpen n]
  obtain ⟨m, hm⟩ := h ((2 : ℚ≥0) ^ (n + d.offset))
  exact ⟨m, hm⟩

end ComputableMartingale

/-- **Martin-Löf randomness implies computable randomness.** -/
theorem IsMartinLofRandom.isComputablyRandom {x : Cantor} (h : IsMartinLofRandom x) :
    IsComputablyRandom x :=
  fun d hd ↦ h d.villeTest (ComputableMartingale.captures_villeTest_of_succeeds hd)

end AlgorithmicRandomness
