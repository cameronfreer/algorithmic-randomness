/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.TotalCode
import AlgorithmicRandomness.Randomness.Schnorr

/-!
# No computable point is Schnorr random

Given a point of Cantor space together with a program computing its bits, we build a Schnorr
test capturing it. The construction is uniform in the point's code, so this supersedes the
constant-`true` prototype of the coding spike.

The pieces are:

* `prefixAt`, a fuel-bounded assembly of an initial segment, primitive recursive uniformly in
  the code, the fuel, and the length;
* `prefixFamilyCode`, whose `n`-th open set is exactly the cylinder on `p ↾ n`;
* `stageSearch`, the search for a stage at which that cylinder has been enumerated — defined as
  a partial recursive function whose *termination* is proved from the point-code's totality, so
  that no explicit bound on `evaln` fuel is ever needed;
* the modulus, obtained by bundling that search with `NatFunctionCode.ofPartrecTotal`.

Because the open sets are exactly attained at a finite stage, the tail is literally empty and
the modulus does not depend on `k` at all.
-/

open Nat.Partrec (Code)
open MeasureTheory
open scoped ENNReal

namespace AlgorithmicRandomness

/-- A point of Cantor space together with a program computing its bits. -/
structure ComputableCantorPoint where
  /-- The point. -/
  point : Cantor
  /-- A program computing its bits. -/
  bitCode : Code
  /-- The evaluation witness. -/
  eval_bitCode : ∀ n, bitCode.eval n = Part.some (Encodable.encode (point n))

namespace ComputableCantorPoint

variable (p : ComputableCantorPoint)

/-- The initial segment of length `n`, from the Cantor layer. -/
abbrev prefixOf (n : ℕ) : BitString := initSeg p.point n

theorem prefixOf_succ (n : ℕ) : p.prefixOf (n + 1) = p.prefixOf n ++ [p.point n] :=
  initSeg_succ p.point n

theorem length_prefixOf (n : ℕ) : (p.prefixOf n).length = n := length_initSeg p.point n

theorem mem_cylinder_prefixOf (n : ℕ) : p.point ∈ cylinder (p.prefixOf n) :=
  mem_cylinder_initSeg p.point n

end ComputableCantorPoint

/-! ## Fuel-bounded prefix assembly -/

/-- Assemble the first `n` bits produced by `c` at fuel `s`; `none` if any has not converged. -/
def prefixAt (c : Code) (s n : ℕ) : Option BitString :=
  Nat.rec (some []) (fun i acc ↦ acc.bind fun L ↦
    ((Code.evaln s c i).bind (Encodable.decode : ℕ → Option Bool)).map fun b ↦ L ++ [b]) n

@[simp] theorem prefixAt_zero (c : Code) (s : ℕ) : prefixAt c s 0 = some [] := rfl

@[simp] theorem prefixAt_succ (c : Code) (s n : ℕ) :
    prefixAt c s (n + 1) = (prefixAt c s n).bind fun L ↦
      ((Code.evaln s c n).bind (Encodable.decode : ℕ → Option Bool)).map fun b ↦ L ++ [b] := rfl

theorem primrec_prefixAt : Primrec fun z : (Code × ℕ) × ℕ ↦ prefixAt z.1.1 z.1.2 z.2 := by
  unfold prefixAt
  refine (Primrec.nat_rec (α := Code × ℕ)
    (f := fun _ : Code × ℕ ↦ (some [] : Option BitString))
    (g := fun (z : Code × ℕ) (q : ℕ × Option BitString) ↦
      q.2.bind fun L ↦ ((Code.evaln z.2 z.1 q.1).bind
        (Encodable.decode : ℕ → Option Bool)).map fun b ↦ L ++ [b])
    (Primrec.const _) ?_).comp Primrec.fst Primrec.snd
  refine Primrec.option_bind (Primrec.snd.comp Primrec.snd) ?_
  refine Primrec.option_map ?_ ?_
  · refine Primrec.option_bind ?_ (Primrec.decode.comp Primrec.snd)
    exact Code.primrec_evaln.comp
      (((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  · exact Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))

theorem prefixAt_mono {c : Code} {s t n : ℕ} {σ : BitString} (h : s ≤ t)
    (hs : prefixAt c s n = some σ) : prefixAt c t n = some σ := by
  induction n generalizing σ with
  | zero => simpa using hs
  | succ n ih =>
    rw [prefixAt_succ, Option.bind_eq_some_iff] at hs
    obtain ⟨L, hL, hrest⟩ := hs
    rw [Option.map_eq_some_iff] at hrest
    obtain ⟨b, hb, rfl⟩ := hrest
    rw [Option.bind_eq_some_iff] at hb
    obtain ⟨m, hm, hdec⟩ := hb
    rw [prefixAt_succ, ih hL, Option.bind_some, Code.evaln_mono h hm, Option.bind_some, hdec]
    rfl

theorem prefixAt_eq (p : ComputableCantorPoint) {s n : ℕ} {σ : BitString}
    (h : prefixAt p.bitCode s n = some σ) : σ = p.prefixOf n := by
  induction n generalizing σ with
  | zero => simpa using h.symm
  | succ n ih =>
    rw [prefixAt_succ, Option.bind_eq_some_iff] at h
    obtain ⟨L, hL, hrest⟩ := h
    rw [Option.map_eq_some_iff] at hrest
    obtain ⟨b, hb, rfl⟩ := hrest
    rw [Option.bind_eq_some_iff] at hb
    obtain ⟨m, hm, hdec⟩ := hb
    have hmem : m ∈ p.bitCode.eval n := Code.evaln_sound hm
    rw [p.eval_bitCode n, Part.mem_some_iff] at hmem
    subst hmem
    rw [Encodable.encodek] at hdec
    have hb : b = p.point n := (Option.some_injective _ hdec).symm
    rw [ih hL, hb, p.prefixOf_succ]

theorem exists_prefixAt (p : ComputableCantorPoint) (n : ℕ) :
    ∃ s, prefixAt p.bitCode s n = some (p.prefixOf n) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht⟩ := Code.evaln_complete.mp
      (by rw [p.eval_bitCode n]; exact Part.mem_some _)
    refine ⟨max s t, ?_⟩
    rw [prefixAt_succ, prefixAt_mono (le_max_left s t) hs, Option.bind_some,
      Code.evaln_mono (le_max_right s t) ht, Option.bind_some, Encodable.encodek]
    rw [Option.map_some, p.prefixOf_succ]

/-! ## The prefix-family code -/

/-- On paired input `⟨n, j⟩`, output the code of `p ↾ n`, ignoring `j`. -/
def prefixEnum (c : Code) : ℕ →. ℕ := fun input ↦
  (Nat.rfind fun s ↦ Part.some (prefixAt c s input.unpair.1).isSome).map
    fun s ↦ Encodable.encode ((prefixAt c s input.unpair.1).getD [])

theorem partrec_prefixEnumUniform : Partrec fun z : Code × ℕ ↦ prefixEnum z.1 z.2 := by
  have hpre : Primrec fun q : (Code × ℕ) × ℕ ↦ prefixAt q.1.1 q.2 q.1.2.unpair.1 :=
    primrec_prefixAt.comp
      (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
  refine Partrec.map (Partrec.rfind ?_) ?_
  · exact Computable₂.partrec₂ (primrec_isSome.comp hpre).to_comp.to₂
  · exact (Primrec.encode.comp ((Primrec.option_getD).comp hpre (Primrec.const []))).to_comp.to₂

theorem partrec_prefixEnum (c : Code) : Nat.Partrec (prefixEnum c) :=
  Partrec.nat_iff.mp ((partrec_prefixEnumUniform.comp
    (Computable.pair (Computable.const c) Computable.id)).of_eq fun _ ↦ rfl)

/-- The uniform prefix-family code, obtained from the uniform computability theorem. -/
noncomputable def prefixFamilyCode (c : Code) : Code :=
  (Code.exists_code.mp (partrec_prefixEnum c)).choose

theorem eval_prefixFamilyCode (c : Code) : (prefixFamilyCode c).eval = prefixEnum c :=
  (Code.exists_code.mp (partrec_prefixEnum c)).choose_spec

namespace ComputableCantorPoint

variable (p : ComputableCantorPoint)

/-- The uniformly c.e. family of prefix cylinders of `p`. -/
noncomputable def prefixOpen : UniformOpenCode := ⟨prefixFamilyCode p.bitCode⟩

theorem eval_prefixFamily_pair (n j : ℕ) :
    (prefixFamilyCode p.bitCode).eval (Nat.pair n j) =
      Part.some (Encodable.encode (p.prefixOf n)) := by
  obtain ⟨s, hs⟩ := exists_prefixAt p n
  obtain ⟨t, htmem, -⟩ := Nat.rfind_min'
    (p := fun s ↦ (prefixAt p.bitCode s (Nat.pair n j).unpair.1).isSome) (m := s)
    (by simp [hs])
  have htsome : (prefixAt p.bitCode t n).isSome := by
    have := Nat.rfind_spec htmem; simpa using this
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp htsome
  rw [eval_prefixFamilyCode, prefixEnum, Part.eq_some_iff, Part.mem_map_iff]
  refine ⟨t, htmem, ?_⟩
  simp only [Nat.unpair_pair, hτ, Option.getD_some]
  rw [prefixAt_eq p hτ]

theorem enumeratesString_prefixFamily {n : ℕ} {σ : BitString} :
    EnumeratesString (prefixFamilyCode p.bitCode) n σ ↔ σ = p.prefixOf n := by
  constructor
  · rintro ⟨j, m, hm, hdec⟩
    rw [p.eval_prefixFamily_pair n j, Part.mem_some_iff] at hm
    subst hm
    rw [Encodable.encodek] at hdec
    exact (Option.some_injective _ hdec).symm
  · rintro rfl
    exact ⟨0, Encodable.encode (p.prefixOf n),
      by rw [p.eval_prefixFamily_pair n 0]; exact Part.mem_some _, Encodable.encodek _⟩

theorem denote_prefixOpen (n : ℕ) : p.prefixOpen.denote n = cylinder (p.prefixOf n) := by
  ext x
  rw [UniformOpenCode.mem_denote_iff_enumerates]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    rwa [p.enumeratesString_prefixFamily.mp hσ] at hx
  · intro hx
    exact ⟨p.prefixOf n, p.enumeratesString_prefixFamily.mpr rfl, hx⟩

theorem fairCoin_denote_prefixOpen (n : ℕ) :
    fairCoin (p.prefixOpen.denote n) = (2⁻¹ : ℝ≥0∞) ^ n := by
  rw [p.denote_prefixOpen n, fairCoin_cylinder, p.length_prefixOf]

end ComputableCantorPoint

/-! ## The stage search and the modulus -/

/-- Search for a stage at which level `n` has been enumerated. Enumeration index `0` suffices,
since every index yields the same string. Termination is a theorem, not a fuel estimate. -/
def stageSearch (c : Code) : ℕ →. ℕ := fun input ↦
  Nat.rfind fun s ↦ Part.some (stringOut c s (Nat.pair input.unpair.1 0)).isSome

/-- The uniform statement, required to substantiate the transformation for an arbitrary point
code rather than merely to construct one modulus. -/
theorem partrec_stageSearchUniform : Partrec fun z : Code × ℕ ↦ stageSearch z.1 z.2 := by
  have hout : Primrec fun q : (Code × ℕ) × ℕ ↦
      stringOut q.1.1 q.2 (Nat.pair q.1.2.unpair.1 0) :=
    primrec_stringOut.comp
      (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.const 0)))
  exact Partrec.rfind (Computable₂.partrec₂ (primrec_isSome.comp hout).to_comp.to₂)

theorem partrec_stageSearch (c : Code) : Nat.Partrec (stageSearch c) :=
  Partrec.nat_iff.mp ((partrec_stageSearchUniform.comp
    (Computable.pair (Computable.const c) Computable.id)).of_eq fun _ ↦ rfl)

namespace ComputableCantorPoint

variable (p : ComputableCantorPoint)

theorem exists_stringOut (n : ℕ) :
    ∃ s, stringOut (prefixFamilyCode p.bitCode) s (Nat.pair n 0) = some (p.prefixOf n) := by
  obtain ⟨s, hs⟩ := Code.evaln_complete.mp
    (by rw [p.eval_prefixFamily_pair n 0]; exact Part.mem_some _)
  exact ⟨s, by rw [stringOut, hs, Option.bind_some, Encodable.encodek]⟩

/-- Termination of the search, from the point-code's totality. -/
theorem stageSearch_dom (input : ℕ) : (stageSearch (prefixFamilyCode p.bitCode) input).Dom := by
  obtain ⟨s, hs⟩ := p.exists_stringOut input.unpair.1
  obtain ⟨t, htmem, -⟩ := Nat.rfind_min'
    (p := fun s ↦ (stringOut (prefixFamilyCode p.bitCode) s (Nat.pair input.unpair.1 0)).isSome)
    (m := s) (by rw [hs]; rfl)
  exact Part.dom_iff_mem.mpr ⟨t, htmem⟩

/-- The Schnorr modulus: the bundled stage search. -/
noncomputable def modulusCode : NatFunctionCode :=
  NatFunctionCode.ofPartrecTotal (partrec_stageSearch _) p.stageSearch_dom

theorem stringOut_modulus (n k : ℕ) :
    stringOut (prefixFamilyCode p.bitCode) (p.modulusCode.apply₂ n k) (Nat.pair n 0)
      = some (p.prefixOf n) := by
  have hmem : p.modulusCode.apply₂ n k ∈
      stageSearch (prefixFamilyCode p.bitCode) (Nat.pair n k) := by
    rw [NatFunctionCode.apply₂, modulusCode, NatFunctionCode.ofPartrecTotal_toFun]
    exact Part.get_mem _
  have hspec := Nat.rfind_spec hmem
  simp only [Nat.unpair_pair, Part.mem_some_iff] at hspec
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hspec.symm
  obtain ⟨s, hs⟩ := p.exists_stringOut n
  have h1 := stringOut_mono (le_max_left (p.modulusCode.apply₂ n k) s) hτ
  have h2 := stringOut_mono (le_max_right (p.modulusCode.apply₂ n k) s) hs
  rw [hτ, Option.some_injective _ (h1.symm.trans h2)]

/-- The search stage has saturated the open set. -/
theorem stageSet_modulus_eq (n k : ℕ) :
    p.prefixOpen.stageSet n (p.modulusCode.apply₂ n k) = p.prefixOpen.denote n := by
  refine Set.Subset.antisymm (UniformOpenCode.stageSet_subset_denote _ _ _) ?_
  rw [p.denote_prefixOpen n]
  refine fun x hx ↦ UniformOpenCode.mem_stageSet.mpr ⟨p.prefixOf n, ?_, hx⟩
  exact mem_stringStage.mpr ⟨0, Nat.zero_le _, p.stringOut_modulus n k⟩

/-- Because the open sets are exactly attained, the tail is literally empty. -/
theorem tail_empty (n k : ℕ) :
    p.prefixOpen.denote n \ p.prefixOpen.stageSet n (p.modulusCode.apply₂ n k) = ∅ := by
  rw [p.stageSet_modulus_eq n k, Set.sdiff_self]

/-- The Schnorr test capturing `p`. -/
noncomputable def schnorrTest : SchnorrTest where
  toMartinLofTest := ⟨p.prefixOpen, fun n ↦ le_of_eq (p.fairCoin_denote_prefixOpen n)⟩
  modulus := p.modulusCode
  tail_le n k := by
    show fairCoin (p.prefixOpen.denote n \ p.prefixOpen.stageSet n _) ≤ _
    rw [p.tail_empty n k]
    simp

@[simp]
theorem schnorrTest_openCode : p.schnorrTest.openCode = p.prefixOpen := rfl

theorem captures_schnorrTest : p.schnorrTest.Captures p.point := fun n ↦ by
  rw [schnorrTest_openCode, p.denote_prefixOpen n]
  exact p.mem_cylinder_prefixOf n

/-- No computable point of Cantor space is Schnorr random. -/
theorem not_isSchnorrRandom : ¬IsSchnorrRandom p.point :=
  not_isSchnorrRandom_of_captures p.captures_schnorrTest

/-- Hence no computable point is Martin-Löf random either. -/
theorem not_isMartinLofRandom : ¬IsMartinLofRandom p.point :=
  fun h ↦ p.not_isSchnorrRandom h.isSchnorrRandom

end ComputableCantorPoint

/-! ## Consistency with the coding-spike prototype

The constant-`true` point is an instance of the general construction, so the Phase 5 result
`not_isMartinLofRandom_const_true` — proved there from the hand-built `replicateTrueOpen` —
is recovered here from an arbitrary coded point. -/

/-- The constant-`true` point, as a coded computable point. -/
def constTruePoint : ComputableCantorPoint where
  point := fun _ ↦ true
  bitCode := Code.const (Encodable.encode true)
  eval_bitCode _ := Code.eval_const _ _

theorem not_isSchnorrRandom_const_true : ¬IsSchnorrRandom (fun _ ↦ true) :=
  constTruePoint.not_isSchnorrRandom

end AlgorithmicRandomness
