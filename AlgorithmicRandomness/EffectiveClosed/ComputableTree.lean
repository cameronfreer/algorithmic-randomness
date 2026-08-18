/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.FiniteOpen
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

end AlgorithmicRandomness
