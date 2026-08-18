/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Complexity.PrefixComplexity
import AlgorithmicRandomness.Randomness.MartinLof

/-!
# Martin-Löf randomness implies incompressibility

A Martin-Löf random point has initial segments of near-maximal prefix complexity: there is a
constant `c` with `m ≤ K(x ↾ m) + c` for every `m`. The constant is not bookkeeping — it is
exactly the level of the compression test at which randomness escapes.

The test at level `c` collects the strings `τ` with `K(τ) + c < |τ|`. Its measure bound is the
*finite* Kraft inequality, applied once per stage:

* each enumerated `τ` has a shortest description `p` with `|p| + c < |τ|`, so
  `weight τ ≤ 2⁻¹ ^ c * weight p`;
* distinct `τ` have distinct such `p`, because a description determines its output
  (`PrefixMachine.describes_unique`);
* those `p` lie in the universal machine's domain, which is prefix-free, so their weights sum to
  at most one (`totalWeight_le_one_of_prefixFree`).

Injectivity is load-bearing rather than decorative: summing `2⁻¹ ^ |p|` over a *multiset* of
descriptions is not bounded by one, so without it the estimate would be false while looking
right.

No infinite Kraft sum appears. Every measure statement is a finite `Finset` sum in `ℚ≥0`, crossing
to `ℝ≥0∞` exactly once through `fairCoin_denote_le_iff`.
-/

open MeasureTheory
open Nat.Partrec (Code)
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

open BitString

/-! ## Compressibility at a level -/

/-- `τ` is seen to be `c`-compressible by stage `s`. -/
noncomputable def compressibleAt (c s : ℕ) (τ : BitString) : Bool :=
  match prefixComplexityStage s τ with
  | none => false
  | some l => decide (l + c < τ.length)

theorem compressibleAt_iff {c s : ℕ} {τ : BitString} :
    compressibleAt c s τ = true ↔ ∃ l, prefixComplexityStage s τ = some l ∧ l + c < τ.length := by
  rw [compressibleAt]
  cases h : prefixComplexityStage s τ with
  | none => simp
  | some l => simp

/-- **The enumeration is exactly compressibility.** Soundness of the stage gives one direction and
completeness the other. -/
theorem exists_compressibleAt_iff {c : ℕ} {τ : BitString} :
    (∃ s, compressibleAt c s τ = true) ↔ prefixComplexity τ + c < τ.length := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨l, hl, hlt⟩ := compressibleAt_iff.mp hs
    exact lt_of_le_of_lt (Nat.add_le_add_right (prefixComplexityStage_sound hl) c) hlt
  · intro h
    obtain ⟨s, hs⟩ := prefixComplexityStage_complete τ
    exact ⟨s, compressibleAt_iff.mpr ⟨_, hs, h⟩⟩

theorem primrec_compressibleAt :
    Primrec fun z : (ℕ × ℕ) × BitString ↦ compressibleAt z.1.1 z.1.2 z.2 := by
  have hstage : Primrec fun z : (ℕ × ℕ) × BitString ↦ prefixComplexityStage z.1.2 z.2 :=
    primrec_prefixComplexityStage.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hbody : Primrec₂ fun (z : (ℕ × ℕ) × BitString) (l : ℕ) ↦
      decide (l + z.1.1 < z.2.length) :=
    (primrecPred_iff_primrec_decide.mp
      (Primrec.nat_lt.comp
        (Primrec.nat_add.comp Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))).to₂
  refine (Primrec.option_casesOn hstage (Primrec.const false) hbody).of_eq fun z ↦ ?_
  simp only [compressibleAt]
  cases prefixComplexityStage z.1.2 z.2 <;> rfl

-- `compressibleAt` unfolds through the whole complexity approximation; the interpreter
-- composition below times out in `whnf` otherwise.
attribute [local irreducible] compressibleAt

/-! ## The compression test -/

/-- At level `c`, on the encoding of `τ`, search for a stage witnessing `c`-compressibility. The
search is over the *approximation stage*, which is the genuinely existential quantity; the string
itself is the branch input rather than a searched value. -/
noncomputable def compressEnum (input : ℕ) : Part ℕ :=
  (Part.ofOption (canonicalBitString input.unpair.2)).bind fun τ ↦
    (Nat.rfind fun s ↦ Part.some (compressibleAt input.unpair.1 s τ)).map fun _ ↦
      Encodable.encode τ

theorem partrec_compressEnum : Nat.Partrec compressEnum := by
  refine Partrec.nat_iff.mp (Partrec.bind (Computable.ofOption ?_) ?_)
  · exact (primrec_canonicalBitString.comp (Primrec.snd.comp Primrec.unpair)).to_comp
  · refine Partrec.map (Partrec.rfind ?_) ?_
    · have h : Computable fun w : (ℕ × BitString) × ℕ ↦
          compressibleAt w.1.1.unpair.1 w.2 w.1.2 :=
        (primrec_compressibleAt.comp
          (Primrec.pair
            (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
              Primrec.snd)
            (Primrec.snd.comp Primrec.fst))).to_comp
      exact Computable₂.partrec₂ h.to₂
    · exact (Primrec.encode.comp (Primrec.snd.comp Primrec.fst)).to_comp.to₂

noncomputable def compressCode : Code := (Code.exists_code.mp partrec_compressEnum).choose

theorem eval_compressCode : compressCode.eval = compressEnum :=
  (Code.exists_code.mp partrec_compressEnum).choose_spec

/-- The coded family: level `c` is the set of `c`-compressible strings. -/
noncomputable def compressOpen : UniformOpenCode := ⟨compressCode⟩

@[simp] theorem compressOpen_program : compressOpen.program = compressCode := rfl

theorem enumeratesString_compressCode {c : ℕ} {τ : BitString} :
    EnumeratesString compressCode c τ ↔ prefixComplexity τ + c < τ.length := by
  constructor
  · rintro ⟨k, m, hm, hdec⟩
    rw [eval_compressCode, compressEnum, Nat.unpair_pair, Part.mem_bind_iff] at hm
    obtain ⟨ρ, hρ, hm'⟩ := hm
    rw [Part.mem_ofOption] at hρ
    rw [Part.mem_map_iff] at hm'
    obtain ⟨s, hs, rfl⟩ := hm'
    rw [Encodable.encodek, Option.some_inj] at hdec
    subst hdec
    exact exists_compressibleAt_iff.mp ⟨s, by simpa using Nat.rfind_spec hs⟩
  · intro h
    obtain ⟨s, hs⟩ := exists_compressibleAt_iff.mpr h
    obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun t ↦ compressibleAt c t τ) hs
    refine ⟨Encodable.encode τ, Encodable.encode τ, ?_, Encodable.encodek τ⟩
    rw [eval_compressCode, compressEnum, Nat.unpair_pair, Part.mem_bind_iff]
    refine ⟨τ, ?_, (Part.mem_map_iff _).mpr ⟨n, hn, rfl⟩⟩
    rw [Part.mem_ofOption, canonicalBitString_encode]
    rfl

/-- **The semantic characterization**: a point is at level `c` exactly when some `c`-compressible
string is one of its prefixes. -/
theorem mem_denote_compressOpen {x : Cantor} {c : ℕ} :
    x ∈ compressOpen.denote c ↔
      ∃ τ, prefixComplexity τ + c < τ.length ∧ x ∈ cylinder τ := by
  rw [UniformOpenCode.mem_denote_iff_enumerates]
  simp only [compressOpen_program, enumeratesString_compressCode]

/-! ## The measure bound

A chosen shortest description per string. Private: the stable semantic API is
`exists_describes_length_prefixComplexity`, and the particular minimizer is a proof artifact. -/

private noncomputable def shortestDescription (τ : BitString) : BitString :=
  (exists_describes_length_prefixComplexity τ).choose

private theorem length_shortestDescription (τ : BitString) :
    (shortestDescription τ).length = prefixComplexity τ :=
  (exists_describes_length_prefixComplexity τ).choose_spec.1

private theorem describes_shortestDescription (τ : BitString) :
    PrefixMachine.Describes universalPrefixCode (shortestDescription τ) τ :=
  (exists_describes_length_prefixComplexity τ).choose_spec.2

/-- **Injectivity**, and the step the estimate would silently fail without: a description
determines its output. -/
private theorem shortestDescription_injective : Function.Injective shortestDescription := by
  intro τ τ' h
  exact PrefixMachine.describes_unique (h ▸ describes_shortestDescription τ)
    (describes_shortestDescription τ')

private theorem weight_le_of_compressible {c : ℕ} {τ : BitString}
    (h : prefixComplexity τ + c < τ.length) :
    BitString.weight τ ≤ 2⁻¹ ^ c * BitString.weight (shortestDescription τ) := by
  rw [BitString.weight, BitString.weight, length_shortestDescription, ← pow_add]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem stageWeight_compress_le (c s : ℕ) : compressOpen.stageWeight c s ≤ 2⁻¹ ^ c := by
  have hmem : ∀ τ ∈ compressOpen.stage c s, prefixComplexity τ + c < τ.length := fun τ hτ ↦
    enumeratesString_compressCode.mp (stringStage_sound hτ)
  have hpf : PrefixFree (((compressOpen.stage c s).image shortestDescription : Finset BitString) :
      Set BitString) := by
    refine Set.Pairwise.mono ?_ isPrefixFreeMachine_universalPrefixCode
    rintro p hp
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
    obtain ⟨τ, -, rfl⟩ := hp
    exact (describes_shortestDescription τ).mem_machineDomain
  calc compressOpen.stageWeight c s
      ≤ totalWeight (compressOpen.stage c s) :=
        totalWeight_mono (minimize_subset _)
    _ ≤ ∑ τ ∈ compressOpen.stage c s, 2⁻¹ ^ c * BitString.weight (shortestDescription τ) :=
        Finset.sum_le_sum fun τ hτ ↦ weight_le_of_compressible (hmem τ hτ)
    _ = 2⁻¹ ^ c * totalWeight ((compressOpen.stage c s).image shortestDescription) := by
        rw [totalWeight, Finset.sum_image fun a _ b _ h ↦ shortestDescription_injective h,
          Finset.mul_sum]
    _ ≤ 2⁻¹ ^ c * 1 := by gcongr; exact totalWeight_le_one_of_prefixFree hpf
    _ = 2⁻¹ ^ c := mul_one _

/-- The bound in the form the test needs. Isolated rather than left to `exact_mod_cast`: the
`ℚ≥0`-to-`ℝ≥0∞` step has been a recurring source of elaboration failures. -/
theorem coe_stageWeight_compress_le (c s : ℕ) :
    ((compressOpen.stageWeight c s : ℚ≥0) : ℝ≥0∞) ≤ (2⁻¹ : ℝ≥0∞) ^ c := by
  rw [← coe_pow_inv_two c, coe_le_coe_nnrat]
  exact stageWeight_compress_le c s

noncomputable def compressTest : MartinLofTest where
  openCode := compressOpen
  measure_le c :=
    (UniformOpenCode.fairCoin_denote_le_iff compressOpen c _).mpr
      (coe_stageWeight_compress_le c)

/-- **The capture characterization**, which makes the randomness theorem transparent. -/
theorem captures_compressTest_iff {x : Cantor} :
    compressTest.Captures x ↔ ∀ c, ∃ m, prefixComplexity (initSeg x m) + c < m := by
  constructor
  · intro h c
    obtain ⟨τ, hτ, hx⟩ := mem_denote_compressOpen.mp (h c)
    refine ⟨τ.length, ?_⟩
    rw [initSeg_of_mem_cylinder hx]
    exact hτ
  · intro h c
    obtain ⟨m, hm⟩ := h c
    exact mem_denote_compressOpen.mpr
      ⟨initSeg x m, by rwa [length_initSeg], mem_cylinder_initSeg x m⟩

/-! ## The theorem -/

/-- **Martin-Löf randomness implies incompressibility.** The constant is the level of the
compression test at which `x` escapes. -/
theorem IsMartinLofRandom.prefixComplexity_lowerBound {x : Cantor} (h : IsMartinLofRandom x) :
    ∃ c, ∀ m, m ≤ prefixComplexity (initSeg x m) + c := by
  have hnc := h compressTest
  rw [captures_compressTest_iff] at hnc
  push Not at hnc
  obtain ⟨c, hc⟩ := hnc
  exact ⟨c, hc⟩

end AlgorithmicRandomness
