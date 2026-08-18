/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.FiniteOpen
import AlgorithmicRandomness.Coding.NNRatCode
import AlgorithmicRandomness.Coding.TotalCode

/-!
# Computable trees and effectively closed classes

A tree is a prefix-closed set of finite strings; its *path set* is the collection of infinite
sequences all of whose initial segments lie in the tree. Path sets are exactly the closed subsets
of Cantor space, and when the tree is decidable by a program the path set is an effectively closed
class — the objects Kurtz randomness is defined against.

The root is deliberately not required to be a node. With no nodes at all the path set is empty,
which is the closed class one wants `∅` to denote; demanding `[] ∈ nodes` would make the empty
class unrepresentable.

## What prefix closure is for

The forbidden-cylinder characterization and closedness below use only the *family* of nodes: the
complement of the path set is the union of the cylinders of non-nodes, and both directions of that
are membership computations. Prefix closure is carried here but first becomes essential when the
finite level covers are shown to *decrease* and to intersect in the path set.

## Uniformity

This development requires uniform code transformation when downstream executable code must receive
and run another program — trimming, the universal Martin-Löf test, and the tagged universal
prefix-free machine are the cases. No such consumer occurs here: nothing enumerates trees or
receives a tree code dynamically. A pointwise proved-computable construction is therefore
sufficient, as it was for `ComputableMartingale.toComputableLipschitz`.

## Representation

The semantic tree, its Boolean decision function, and the program computing that function are
three separate layers joined by bridges, as everywhere else in this library. Keeping `member`
Boolean is what stops arbitrary program outputs from entering the mathematical definition: relating
the program directly to `σ ∈ nodes` would need a classical decision procedure inside the
correctness statement and would leave the next layer nothing to run.
-/

open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## Trees -/

/-- A prefix-closed set of finite strings. -/
structure CantorTree where
  /-- The nodes of the tree. -/
  nodes : Set BitString
  /-- Every prefix of a node is a node. -/
  prefix_closed : ∀ {σ τ : BitString}, σ ∈ nodes → τ <+: σ → τ ∈ nodes

namespace CantorTree

variable (T : CantorTree)

/-- The infinite sequences all of whose initial segments are nodes. -/
def paths : Set Cantor := {x | ∀ n, initSeg x n ∈ T.nodes}

variable {T}

@[simp] theorem mem_paths_iff {x : Cantor} : x ∈ T.paths ↔ ∀ n, initSeg x n ∈ T.nodes := Iff.rfl

/-- The contrapositive of prefix closure: nothing below a non-node is a node. This is the form the
level covers use. -/
theorem not_mem_of_prefix_of_not_mem {σ τ : BitString} (hστ : σ <+: τ) (hσ : σ ∉ T.nodes) :
    τ ∉ T.nodes := fun hτ ↦ hσ (T.prefix_closed hτ hστ)

/-- **Forbidden cylinders.** A point misses the path set exactly when some non-node is one of its
prefixes. Only the family of nodes is used here; prefix closure is not needed. -/
theorem paths_compl_eq_iUnion_forbidden : (T.paths)ᶜ = ⋃ σ ∈ T.nodesᶜ, cylinder σ := by
  ext x
  simp only [Set.mem_compl_iff, mem_paths_iff, not_forall, Set.mem_iUnion, Set.mem_compl_iff,
    exists_prop]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨initSeg x n, hn, mem_cylinder_initSeg x n⟩
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ.length, by rwa [initSeg_of_mem_cylinder hx]⟩

theorem isClosed_paths (T : CantorTree) : IsClosed T.paths := by
  rw [← isOpen_compl_iff, paths_compl_eq_iUnion_forbidden]
  exact isOpen_biUnion fun σ _ ↦ (isClopen_cylinder σ).isOpen

theorem measurableSet_paths (T : CantorTree) : MeasurableSet T.paths :=
  (isClosed_paths T).measurableSet

/-! ### The two extremes -/

/-- The empty tree, whose path set is empty. This is why the root is not required to be a node. -/
def empty : CantorTree where
  nodes := ∅
  prefix_closed := by simp

@[simp] theorem paths_empty : empty.paths = ∅ := by
  ext x
  simp [paths, empty]

/-- The full tree, whose path set is everything. -/
def full : CantorTree where
  nodes := Set.univ
  prefix_closed := by simp

@[simp] theorem paths_full : full.paths = Set.univ := by
  ext x
  simp [paths, full]

end CantorTree

/-! ## Computable trees -/

/-- A tree together with a Boolean decision procedure for its nodes and a program computing it.
The Boolean layer is what keeps arbitrary program outputs out of the semantic definition; only the
realizing program is intentionally non-unique. -/
structure ComputableTree extends CantorTree where
  /-- The decision procedure. -/
  member : BitString → Bool
  /-- The bridge to the semantic tree, which determines `member` pointwise. -/
  member_iff : ∀ σ, member σ = true ↔ σ ∈ nodes
  /-- The program computing it. -/
  program : NatFunctionCode
  /-- The code-correctness witness. -/
  eval_member : ∀ σ, program.toFun (Encodable.encode σ) = Encodable.encode (member σ)

namespace ComputableTree

variable (T : ComputableTree)

@[simp] theorem member_eq_true_iff (σ : BitString) : T.member σ = true ↔ σ ∈ T.nodes :=
  T.member_iff σ

/-- The complementary form, which keeps the level-cover filtering proofs Boolean while still
allowing a semantic rewrite at the boundary. -/
@[simp] theorem member_eq_false_iff (σ : BitString) : T.member σ = false ↔ σ ∉ T.nodes := by
  rw [← member_eq_true_iff T σ, Bool.eq_false_iff, ne_eq]

theorem computable_member : Computable T.member := by
  have h : Computable fun σ : BitString ↦ Encodable.encode (T.member σ) :=
    T.program.computable_toFun.comp Primrec.encode.to_comp |>.of_eq fun σ ↦ T.eval_member σ
  exact Computable.encode_iff.mp h

end ComputableTree

/-! ## Level fronts

The surviving strings of one length, the clopen set they cover, and its exact rational measure.

Membership is only `Computable`, not `Primrec`, and the pinned mathlib has no `Computable` list
filter or fold. The *count* of survivors is therefore obtained by recursion on the index rather
than by measuring a filtered list — the same escape that let the grid program avoid fuel. The
filter form is kept for the semantic proofs, where it reads better, and
`survivorCount_eq_take_length` is the bridge. -/

namespace ComputableTree

variable (T : ComputableTree)

/-- The nodes of one length. -/
def levelFront (n : ℕ) : List BitString := (BitString.wordsOfLength n).filter T.member

/-- The clopen set they cover. -/
def levelCover (n : ℕ) : Set Cantor := cylinderUnion (T.levelFront n).toFinset

variable {T}

@[simp] theorem mem_levelFront_iff {n : ℕ} {σ : BitString} :
    σ ∈ T.levelFront n ↔ σ.length = n ∧ σ ∈ T.nodes := by
  rw [levelFront, List.mem_filter, ComputableTree.member_eq_true_iff]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨BitString.length_of_mem_wordsOfLength h1, h2⟩,
    fun ⟨h1, h2⟩ ↦ ⟨h1 ▸ BitString.mem_wordsOfLength_length σ, h2⟩⟩

theorem length_of_mem_levelFront {n : ℕ} {σ : BitString} (h : σ ∈ T.levelFront n) :
    σ.length = n := (mem_levelFront_iff.mp h).1

theorem nodup_levelFront (T : ComputableTree) (n : ℕ) : (T.levelFront n).Nodup :=
  (BitString.nodup_wordsOfLength n).filter _

theorem prefixFree_levelFront (T : ComputableTree) (n : ℕ) :
    PrefixFree ((T.levelFront n).toFinset : Set BitString) := by
  rw [prefixFree_iff]
  intro σ hσ τ hτ hpre
  rw [Finset.mem_coe, List.mem_toFinset] at hσ hτ
  exact hpre.eq_of_length
    ((length_of_mem_levelFront hσ).trans (length_of_mem_levelFront hτ).symm)

theorem isClopen_levelCover (T : ComputableTree) (n : ℕ) : IsClopen (T.levelCover n) := by
  rw [levelCover, cylinderUnion]
  refine ⟨Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
      fun σ _ ↦ (isClopen_cylinder σ).isClosed, ?_⟩
  exact isOpen_biUnion fun σ _ ↦ (isClopen_cylinder σ).isOpen

/-- **The intersection characterization.** At a fixed level, lying in a cylinder of that length
identifies the string as the initial segment, so neither inclusion needs prefix closure. -/
theorem paths_eq_iInter_levelCover (T : ComputableTree) :
    T.toCantorTree.paths = ⋂ n, T.levelCover n := by
  ext x
  simp only [CantorTree.mem_paths_iff, Set.mem_iInter, levelCover, mem_cylinderUnion,
    List.mem_toFinset]
  constructor
  · intro h n
    exact ⟨initSeg x n, mem_levelFront_iff.mpr ⟨length_initSeg x n, h n⟩, mem_cylinder_initSeg x n⟩
  · intro h n
    obtain ⟨σ, hσ, hxσ⟩ := h n
    obtain ⟨hlen, hmem⟩ := mem_levelFront_iff.mp hσ
    rwa [← hlen, initSeg_of_mem_cylinder hxσ]

/-- **Antitonicity**, the one consumer of prefix closure in this layer. -/
theorem antitone_levelCover (T : ComputableTree) : Antitone T.levelCover := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  intro x hx
  rw [levelCover, mem_cylinderUnion] at hx ⊢
  obtain ⟨σ, hσ, hxσ⟩ := hx
  rw [List.mem_toFinset] at hσ
  obtain ⟨hlen, hmem⟩ := mem_levelFront_iff.mp hσ
  refine ⟨initSeg x n, List.mem_toFinset.mpr (mem_levelFront_iff.mpr ⟨length_initSeg x n, ?_⟩),
    mem_cylinder_initSeg x n⟩
  refine T.prefix_closed hmem ?_
  have hσeq : initSeg x (n + 1) = σ := by rw [← hlen]; exact initSeg_of_mem_cylinder hxσ
  rw [← hσeq]
  exact initSeg_prefix_of_le (Nat.le_succ n)

/-! ## Counting survivors -/

/-- The survivors among the first `k` strings of length `n`, by recursion on the index. -/
def survivorCount (T : ComputableTree) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => survivorCount T n k
      + (if T.member ((BitString.wordsOfLength n).getD k []) then 1 else 0)

/-- The induction invariant. The bound is necessary: past the end of the list `getD` would start
counting the default string. -/
theorem survivorCount_eq_take_length (T : ComputableTree) (n : ℕ) : ∀ {k : ℕ}, k ≤ 2 ^ n →
    survivorCount T n k = (((BitString.wordsOfLength n).take k).filter T.member).length := by
  intro k
  induction k with
  | zero => intro _; rw [survivorCount, List.take_zero, List.filter_nil, List.length_nil]
  | succ k ih =>
    intro hk
    have hklt : k < (BitString.wordsOfLength n).length := by
      rw [BitString.length_wordsOfLength]; omega
    rw [survivorCount, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hklt,
      Option.toList_some, List.filter_append, List.length_append,
      List.getD_eq_getElem _ _ hklt]
    by_cases hm : T.member (BitString.wordsOfLength n)[k] = true
    · rw [List.filter_cons_of_pos hm, if_pos hm]
      simp
    · rw [List.filter_cons_of_neg hm, if_neg hm]
      simp

theorem survivorCount_eq_length (T : ComputableTree) (n : ℕ) :
    survivorCount T n (2 ^ n) = (T.levelFront n).length := by
  rw [survivorCount_eq_take_length T n (le_refl _), levelFront,
    List.take_of_length_le (by rw [BitString.length_wordsOfLength])]

theorem computable_survivorCount (T : ComputableTree) :
    Computable fun p : ℕ × ℕ ↦ survivorCount T p.1 p.2 := by
  have hbool : Computable fun w : (ℕ × ℕ) × (ℕ × ℕ) ↦
      T.member ((BitString.wordsOfLength w.1.1).getD w.2.1 []) :=
    T.computable_member.comp
      ((Primrec.list_getD ([] : BitString)).comp
        (BitString.primrec_wordsOfLength.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd)).to_comp
  have hmain : Computable fun w : (ℕ × ℕ) × (ℕ × ℕ) ↦
      w.2.2 + (if T.member ((BitString.wordsOfLength w.1.1).getD w.2.1 []) then 1 else 0) := by
    refine (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.cond hbool (Computable.const 1) (Computable.const 0))).of_eq fun w ↦ ?_
    cases T.member ((BitString.wordsOfLength w.1.1).getD w.2.1 []) <;> simp
  refine (Computable.nat_rec (f := fun p : ℕ × ℕ ↦ p.2)
    (g := fun _ : ℕ × ℕ ↦ 0) Computable.snd (Computable.const 0) hmain.to₂).of_eq fun p ↦ ?_
  obtain ⟨n, k⟩ := p
  induction k with
  | zero => rfl
  | succ k ih => rw [survivorCount, ← ih]

/-! ## Exact rational measure -/

/-- The measure of the level cover, exact in `ℚ≥0` and defined from the executable count. -/
def levelWeight (T : ComputableTree) (n : ℕ) : ℚ≥0 :=
  (survivorCount T n (2 ^ n) : ℚ≥0) * (2⁻¹ : ℚ≥0) ^ n

theorem fairCoin_levelCover (T : ComputableTree) (n : ℕ) :
    fairCoin (T.levelCover n) = ((T.levelWeight n : ℚ≥0) : ℝ≥0∞) := by
  rw [levelCover, fairCoin_cylinderUnion_of_prefixFree (prefixFree_levelFront T n)]
  congr 1
  rw [levelWeight, survivorCount_eq_length, totalWeight,
    Finset.sum_congr rfl (fun σ hσ ↦ by
      rw [BitString.weight, length_of_mem_levelFront (List.mem_toFinset.mp hσ)]),
    Finset.sum_const, List.toFinset_card_of_nodup (nodup_levelFront T n), nsmul_eq_mul]

/-- The coded rational form, so the search in the next layer never reopens the representation. -/
def levelWeightCode (T : ComputableTree) (n : ℕ) : ℕ :=
  Nat.pair (survivorCount T n (2 ^ n)) (2 ^ n - 1)

theorem value_levelWeightCode (T : ComputableTree) (n : ℕ) :
    NNRatCode.value (T.levelWeightCode n) = T.levelWeight n := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [levelWeightCode, NNRatCode.value_pair, Nat.sub_add_cancel hpos, levelWeight]
  push_cast
  rw [div_eq_mul_inv, ← inv_pow]

theorem computable_levelWeightCode (T : ComputableTree) : Computable T.levelWeightCode := by
  have hcount : Computable fun n : ℕ ↦ survivorCount T n (2 ^ n) :=
    T.computable_survivorCount.comp
      (Computable.pair Computable.id
        ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id).to_comp)
  exact Primrec₂.natPair.to_comp.comp hcount
    (Primrec.nat_sub.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
      (Primrec.const 2) Primrec.id) (Primrec.const 1)).to_comp

/-! ## The termination certificate

Continuity from above for the antitone covers. This is the only semantic input the search in the
next layer needs; the search itself is then purely executable. -/

theorem exists_levelWeight_le_of_null (T : ComputableTree)
    (hnull : fairCoin T.toCantorTree.paths = 0) (k : ℕ) :
    ∃ n, T.levelWeight n ≤ (2⁻¹ : ℚ≥0) ^ k := by
  have htend : Filter.Tendsto (fairCoin ∘ T.levelCover) Filter.atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_measure_iInter_atTop (μ := fairCoin)
      (fun n ↦ ((T.isClopen_levelCover n).1.measurableSet).nullMeasurableSet)
      T.antitone_levelCover ⟨0, measure_ne_top _ _⟩
    rwa [← paths_eq_iInter_levelCover, hnull] at h
  have hpos : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ k :=
    pos_iff_ne_zero.mpr (pow_ne_zero k (by simp))
  obtain ⟨n, hn⟩ :=
    (ENNReal.tendsto_nhds_zero.mp htend ((2⁻¹ : ℝ≥0∞) ^ k) hpos).exists
  refine ⟨n, ?_⟩
  rw [← coe_le_coe_nnrat, coe_pow_inv_two]
  exact le_trans (le_of_eq (fairCoin_levelCover T n).symm) hn

end ComputableTree

end AlgorithmicRandomness
