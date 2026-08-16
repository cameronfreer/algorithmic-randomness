/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.FiniteOpen
import AlgorithmicRandomness.Complexity.PrefixMachine

/-!
# Kraft–Chaitin allocation

Given a computably enumerable stream of requests — each a length and an output — whose weights sum
to at most one, this builds an actual prefix-free machine realizing them: for every request there
is a codeword of exactly the requested length mapping to the requested output.

The allocator maintains *canonical free slots*, which is the substantive part. Searching for any
word of the requested length incomparable with everything allocated is not enough: many longer
assignments can occupy every shorter prefix while Kraft mass remains unused, and the search then
fails on a legal request.

The invariant is that free slots have **strictly decreasing lengths**, everything in play is
pairwise incompatible, and allocated weight plus free weight is exactly one. Fulfilment takes the
**longest adequate slot** — the first, given the ordering — and this is not interchangeable with
the shortest. From `[]`, a length-3 request leaves free lengths `3, 2, 1`; a following length-2
request served from the length-1 slot would produce a second length-2 slot and leave nothing for a
later length-1 request. Served from the existing length-2 slot, the invariant is preserved.

Availability is then a counting argument: distinct lengths all exceeding `n` have total weight
strictly below `2⁻ⁿ`, so a request that still fits inside the Kraft budget must find a slot.
-/

open scoped NNRat

namespace AlgorithmicRandomness

open BitString

/-! ## List weights

The `Finset` weight of the coded layer collapses duplicates. Everything here is pairwise
incompatible and hence duplicate-free, but the inductions run on lists, so a list-level sum is the
convenient form; `listWeight_toFinset` is the bridge. -/

def listWeight (L : List BitString) : ℚ≥0 := (L.map BitString.weight).sum

@[simp] theorem listWeight_nil : listWeight [] = 0 := rfl

@[simp] theorem listWeight_cons (σ : BitString) (L : List BitString) :
    listWeight (σ :: L) = BitString.weight σ + listWeight L := rfl

theorem listWeight_append (L M : List BitString) :
    listWeight (L ++ M) = listWeight L + listWeight M := by
  rw [listWeight, listWeight, listWeight, List.map_append, List.sum_append]

theorem listWeight_toFinset : ∀ {L : List BitString}, L.Nodup → totalWeight L.toFinset
    = listWeight L := by
  intro L
  induction L with
  | nil => intro _; simp [totalWeight, listWeight]
  | cons σ L ih =>
    intro h
    rw [List.nodup_cons] at h
    rw [totalWeight, List.toFinset_cons, Finset.sum_insert (by simpa using h.1),
      ← totalWeight, ih h.2, listWeight_cons]

/-! ## Descending to a requested length

Split a slot down to a target length by repeatedly taking the `false` child and freeing the `true`
sibling. The siblings come out in strictly decreasing length order, deepest first, which is exactly
the order the free list wants. -/

/-- From `σ`, descend `k` levels: the allocated codeword and the freed siblings. -/
def descend (σ : BitString) : ℕ → BitString × List BitString
  | 0 => (σ, [])
  | k + 1 =>
      ((descend (σ ++ [false]) k).1, (descend (σ ++ [false]) k).2 ++ [σ ++ [true]])

@[simp] theorem descend_zero (σ : BitString) : descend σ 0 = (σ, []) := rfl

theorem descend_succ (σ : BitString) (k : ℕ) :
    descend σ (k + 1) =
      ((descend (σ ++ [false]) k).1, (descend (σ ++ [false]) k).2 ++ [σ ++ [true]]) := rfl

theorem descend_fst (σ : BitString) (k : ℕ) :
    (descend σ k).1 = σ ++ List.replicate k false := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
    rw [descend_succ, ih, List.append_assoc, List.replicate_succ]
    rfl

@[simp] theorem length_descend_fst (σ : BitString) (k : ℕ) :
    (descend σ k).1.length = σ.length + k := by
  rw [descend_fst, List.length_append, List.length_replicate]

theorem prefix_descend_fst (σ : BitString) (k : ℕ) : σ <+: (descend σ k).1 := by
  rw [descend_fst]
  exact ⟨_, rfl⟩

theorem length_of_mem_descend_snd {σ : BitString} {k : ℕ} {ρ : BitString}
    (h : ρ ∈ (descend σ k).2) : σ.length < ρ.length ∧ ρ.length ≤ σ.length + k := by
  induction k generalizing σ with
  | zero => simp at h
  | succ k ih =>
    rw [descend_succ] at h
    rcases List.mem_append.mp h with h' | h'
    · obtain ⟨h1, h2⟩ := ih h'
      simp only [List.length_append, List.length_singleton] at h1 h2
      omega
    · rw [List.mem_singleton] at h'
      subst h'
      simp

theorem prefix_of_mem_descend_snd {σ : BitString} {k : ℕ} {ρ : BitString}
    (h : ρ ∈ (descend σ k).2) : σ <+: ρ := by
  induction k generalizing σ with
  | zero => simp at h
  | succ k ih =>
    rw [descend_succ] at h
    rcases List.mem_append.mp h with h' | h'
    · exact (List.prefix_append σ [false]).trans (ih h')
    · rw [List.mem_singleton] at h'
      subst h'
      exact List.prefix_append σ [true]

/-- **The closed form for the siblings.** The recursion in `descend` substitutes into its string
parameter, so it is not in `Primrec.nat_rec` shape; this identity puts it in `list_map` shape
instead, which is what the computability proof needs. -/
theorem descend_snd_eq (σ : BitString) (k : ℕ) :
    (descend σ k).2
      = (List.range k).map fun i ↦ σ ++ List.replicate (k - 1 - i) false ++ [true] := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
    rw [descend_succ, ih, List.range_succ, List.map_append]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun i hi ↦ ?_) (by simp)
    rw [List.mem_range] at hi
    rw [List.append_assoc σ [false], List.singleton_append, ← List.replicate_succ,
      show k - 1 - i + 1 = k + 1 - 1 - i from by omega]

private theorem primrec_replicateFalse : Primrec fun n : ℕ ↦ List.replicate n false := by
  refine (Primrec.list_map Primrec.list_range (Primrec.const false).to₂).of_eq fun n ↦ ?_
  rw [List.map_const', List.length_range]

theorem primrec_descend : Primrec₂ descend := by
  have hfst : Primrec fun z : BitString × ℕ ↦ (descend z.1 z.2).1 := by
    refine (Primrec.list_append.comp Primrec.fst
      (primrec_replicateFalse.comp Primrec.snd)).of_eq fun z ↦ ?_
    rw [descend_fst]
  have hbody : Primrec₂ fun (z : BitString × ℕ) (i : ℕ) ↦
      z.1 ++ List.replicate (z.2 - 1 - i) false ++ [true] :=
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
        (primrec_replicateFalse.comp
          (Primrec.nat_sub.comp
            (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
            Primrec.snd)))
      (Primrec.const [true])).to₂
  have hsnd : Primrec fun z : BitString × ℕ ↦ (descend z.1 z.2).2 :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd) hbody).of_eq fun z ↦
      (descend_snd_eq z.1 z.2).symm
  exact (Primrec.pair hfst hsnd).of_eq fun z ↦ rfl

/-- Sibling lengths strictly decrease, which is what lets the replacement slot straight into a
decreasing free list. -/
theorem pairwise_length_descend_snd (σ : BitString) (k : ℕ) :
    ((descend σ k).2.map List.length).Pairwise (· > ·) := by
  rw [descend_snd_eq, List.map_map, List.pairwise_map]
  refine (List.pairwise_lt_range (n := k)).imp_of_mem ?_
  intro i j hi hj hij
  rw [List.mem_range] at hi hj
  simp only [Function.comp_apply, List.length_append, List.length_replicate,
    List.length_singleton, gt_iff_lt]
  omega

/-- Two prefixes of a common string are comparable. -/
private theorem compatible_of_prefix_common {ρ σ τ : BitString} (hρ : ρ <+: τ) (hσ : σ <+: τ) :
    BitString.Compatible ρ σ := by
  rcases le_total ρ.length σ.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le hρ hσ h)
  · exact Or.inr (List.prefix_of_prefix_length_le hσ hρ h)

/-- **Incompatibility survives refinement.** Anything incompatible with a slot stays incompatible
with everything below it — the single fact that makes the replacement step structural. -/
theorem incompatible_of_prefix_right {ρ σ τ : BitString} (hστ : σ <+: τ)
    (hρσ : ¬BitString.Compatible ρ σ) : ¬BitString.Compatible ρ τ := by
  rintro (h | h)
  · exact hρσ (compatible_of_prefix_common h hστ)
  · exact hρσ (Or.inr (hστ.trans h))

/-- **The splitting weight identity.** -/
theorem weight_descend (σ : BitString) (k : ℕ) :
    BitString.weight σ = BitString.weight (descend σ k).1 + listWeight (descend σ k).2 := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
    have h := ih (σ ++ [false])
    rw [BitString.weight_append_singleton] at h
    have hsib : listWeight [σ ++ [true]] = 2⁻¹ * BitString.weight σ := by
      rw [listWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        BitString.weight_append_singleton]
    rw [descend_succ, listWeight_append, hsib]
    have : ((descend (σ ++ [false]) k).1, (descend (σ ++ [false]) k).2 ++ [σ ++ [true]]).1
        = (descend (σ ++ [false]) k).1 := rfl
    rw [this, ← add_assoc, ← h]
    ring

/-- **The splitting set identity.** With it, incompatibility with the untouched state is
structural rather than a separate computation. -/
theorem cylinder_descend (σ : BitString) (k : ℕ) :
    cylinder σ = cylinder (descend σ k).1 ∪ cylinderUnion (descend σ k).2.toFinset := by
  induction k generalizing σ with
  | zero => simp [cylinderUnion]
  | succ k ih =>
    rw [descend_succ]
    rw [cylinder_eq_union_concat σ, ih (σ ++ [false])]
    ext x
    simp only [Set.mem_union, mem_cylinderUnion, List.mem_toFinset, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro ((hx | ⟨ρ, hρ, hx⟩) | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨ρ, Or.inl hρ, hx⟩
      · exact Or.inr ⟨σ ++ [true], Or.inr rfl, hx⟩
    · rintro (hx | ⟨ρ, hρ | rfl, hx⟩)
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr ⟨ρ, hρ, hx⟩)
      · exact Or.inr hx

/-- Sibling children are incompatible, and everything below one of them stays incompatible with
the other. -/
private theorem not_compatible_of_prefix_false {σ ρ : BitString} (h : σ ++ [false] <+: ρ) :
    ¬BitString.Compatible ρ (σ ++ [true]) := by
  have hne : σ ++ [false] ≠ σ ++ [true] := by simp
  rintro (hc | hc)
  · exact hne ((h.trans hc).eq_of_length (by simp))
  · exact hne ((List.prefix_of_prefix_length_le h (hc.trans (List.prefix_refl ρ))
      (by simp)).eq_of_length (by simp))

/-- **The splitting incompatibility contract.** -/
theorem pairwise_descend (σ : BitString) (k : ℕ) :
    List.Pairwise (fun a b ↦ ¬BitString.Compatible a b)
      ((descend σ k).1 :: (descend σ k).2) := by
  induction k generalizing σ with
  | zero => simp
  | succ k ih =>
    have hall : ∀ ρ ∈ (descend (σ ++ [false]) k).1 :: (descend (σ ++ [false]) k).2,
        ¬BitString.Compatible ρ (σ ++ [true]) := by
      intro ρ hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · exact not_compatible_of_prefix_false (prefix_descend_fst _ _)
      · exact not_compatible_of_prefix_false (prefix_of_mem_descend_snd hρ')
    have hih := ih (σ ++ [false])
    rw [List.pairwise_cons] at hih
    rw [descend_succ, List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with hb' | hb'
      · exact hih.1 b hb'
      · rw [List.mem_singleton] at hb'
        subst hb'
        exact hall _ List.mem_cons_self
    · refine List.pairwise_append.mpr ⟨hih.2, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact hall a (List.mem_cons_of_mem _ ha)

/-! ## The geometric tail, and slot availability

Distinct lengths all at least `m` carry total weight strictly below `2 · 2⁻ᵐ`. The induction runs
on the *increasing* list, peeling the smallest: the tail is then bounded by `2 · 2⁻⁽ˡ⁺¹⁾ = 2⁻ˡ`,
which is exactly the head's own weight. Peeling the largest instead gives a bound weaker by a
factor of three and does not close. -/

def weightSum (lengths : List ℕ) : ℚ≥0 := (lengths.map fun l ↦ (2⁻¹ : ℚ≥0) ^ l).sum

@[simp] theorem weightSum_nil : weightSum [] = 0 := rfl

@[simp] theorem weightSum_cons (l : ℕ) (L : List ℕ) :
    weightSum (l :: L) = (2⁻¹ : ℚ≥0) ^ l + weightSum L := rfl

theorem weightSum_reverse (L : List ℕ) : weightSum L.reverse = weightSum L := by
  rw [weightSum, weightSum, List.map_reverse, List.sum_reverse]

theorem listWeight_eq_weightSum (L : List BitString) :
    listWeight L = weightSum (L.map List.length) := by
  rw [listWeight, weightSum, List.map_map]
  rfl

/-- The doubling identity, named because symbolic powers do not survive `ring` when the exponent
is a variable, and the `2 * ·` form drags in instance search that times out on `ℚ≥0`. Stated
additively for that reason. -/
theorem pow_succ_add_pow_succ (l : ℕ) :
    (2⁻¹ : ℚ≥0) ^ (l + 1) + (2⁻¹ : ℚ≥0) ^ (l + 1) = (2⁻¹ : ℚ≥0) ^ l := by
  rw [pow_succ, ← mul_add]
  norm_num

theorem weightSum_lt_add_self : ∀ {L : List ℕ} {m : ℕ}, L.Pairwise (· < ·) →
    (∀ l ∈ L, m ≤ l) → weightSum L < (2⁻¹ : ℚ≥0) ^ m + (2⁻¹ : ℚ≥0) ^ m := by
  intro L
  induction L with
  | nil =>
    intro m _ _
    rw [weightSum_nil]
    have hpos : (0 : ℚ≥0) < (2⁻¹ : ℚ≥0) ^ m := by positivity
    calc (0 : ℚ≥0) < (2⁻¹ : ℚ≥0) ^ m := hpos
      _ ≤ (2⁻¹ : ℚ≥0) ^ m + (2⁻¹ : ℚ≥0) ^ m := le_add_self
  | cons l L ih =>
    intro m hinc hmin
    rw [List.pairwise_cons] at hinc
    have htail := ih hinc.2 fun l' hl' ↦ hinc.1 l' hl'
    rw [pow_succ_add_pow_succ] at htail
    have hml : (2⁻¹ : ℚ≥0) ^ l ≤ (2⁻¹ : ℚ≥0) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hmin l List.mem_cons_self)
    calc weightSum (l :: L) = (2⁻¹ : ℚ≥0) ^ l + weightSum L := weightSum_cons l L
      _ < (2⁻¹ : ℚ≥0) ^ l + (2⁻¹ : ℚ≥0) ^ l :=
        add_lt_add_of_le_of_lt le_rfl htail
      _ ≤ (2⁻¹ : ℚ≥0) ^ m + (2⁻¹ : ℚ≥0) ^ m := add_le_add hml hml

/-- **Availability.** A free list with strictly decreasing lengths carrying at least `2⁻ⁿ` of mass
must contain a slot of length at most `n`. -/
theorem exists_adequate_slot {free : List BitString} {n : ℕ}
    (hsort : (free.map List.length).Pairwise (· > ·))
    (hmass : (2⁻¹ : ℚ≥0) ^ n ≤ listWeight free) :
    ∃ σ ∈ free, σ.length ≤ n := by
  by_contra hno
  push Not at hno
  have hmin : ∀ l ∈ (free.map List.length).reverse, n + 1 ≤ l := by
    intro l hl
    rw [List.mem_reverse, List.mem_map] at hl
    obtain ⟨σ, hσ, rfl⟩ := hl
    exact hno σ hσ
  have hlt : weightSum (free.map List.length).reverse
      < (2⁻¹ : ℚ≥0) ^ (n + 1) + (2⁻¹ : ℚ≥0) ^ (n + 1) :=
    weightSum_lt_add_self (List.pairwise_reverse.mpr hsort) hmin
  rw [pow_succ_add_pow_succ, weightSum_reverse, ← listWeight_eq_weightSum] at hlt
  exact absurd hmass (not_le.mpr hlt)

/-! ## Requests and allocator state

Structures with `Primcodable` instances transported along equivalences to products, so the
allocator can later be run inside a program. Proofs stay outside the structures: the state is
executable data and the invariant is a separate predicate parameterized by the processed
requests. -/

structure KraftRequest where
  /-- The requested codeword length. -/
  length : ℕ
  /-- The output the codeword should describe. -/
  output : BitString

/-- Equivalence used only to transport `Primcodable`. -/
def KraftRequest.equivProd : KraftRequest ≃ ℕ × BitString where
  toFun r := (r.length, r.output)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

instance : Primcodable KraftRequest := Primcodable.ofEquiv _ KraftRequest.equivProd

theorem primrec_kraftRequest_length : Primrec KraftRequest.length :=
  Primrec.fst.comp (Primrec.of_equiv (e := KraftRequest.equivProd))

theorem primrec_kraftRequest_output : Primrec KraftRequest.output :=
  Primrec.snd.comp (Primrec.of_equiv (e := KraftRequest.equivProd))

def KraftRequest.weight (r : KraftRequest) : ℚ≥0 := (2⁻¹ : ℚ≥0) ^ r.length

def totalRequestWeight (rs : List KraftRequest) : ℚ≥0 := (rs.map KraftRequest.weight).sum

@[simp] theorem totalRequestWeight_nil : totalRequestWeight [] = 0 := rfl

theorem totalRequestWeight_append (rs ss : List KraftRequest) :
    totalRequestWeight (rs ++ ss) = totalRequestWeight rs + totalRequestWeight ss := by
  rw [totalRequestWeight, totalRequestWeight, totalRequestWeight, List.map_append, List.sum_append]

@[simp] theorem totalRequestWeight_singleton (r : KraftRequest) :
    totalRequestWeight [r] = r.weight := by
  rw [totalRequestWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

structure Assignment where
  /-- The allocated codeword. -/
  codeword : BitString
  /-- The output it describes. -/
  output : BitString

def Assignment.equivProd : Assignment ≃ BitString × BitString where
  toFun a := (a.codeword, a.output)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

instance : Primcodable Assignment := Primcodable.ofEquiv _ Assignment.equivProd

theorem primrec_assignment_codeword : Primrec Assignment.codeword :=
  Primrec.fst.comp (Primrec.of_equiv (e := Assignment.equivProd))

theorem primrec_assignment_output : Primrec Assignment.output :=
  Primrec.snd.comp (Primrec.of_equiv (e := Assignment.equivProd))

structure AllocationState where
  /-- Codewords assigned so far, in request order. -/
  assigned : List Assignment
  /-- Unallocated slots, in strictly decreasing length order. -/
  free : List BitString

def AllocationState.equivProd : AllocationState ≃ List Assignment × List BitString where
  toFun st := (st.assigned, st.free)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

instance : Primcodable AllocationState := Primcodable.ofEquiv _ AllocationState.equivProd

theorem primrec_allocationState_assigned : Primrec AllocationState.assigned :=
  Primrec.fst.comp (Primrec.of_equiv (e := AllocationState.equivProd))

theorem primrec_allocationState_free : Primrec AllocationState.free :=
  Primrec.snd.comp (Primrec.of_equiv (e := AllocationState.equivProd))

/-! ## Selecting the longest adequate slot

With the free list in decreasing-length order, the first slot of length at most `n` is the longest
adequate one. Written as a structural recursion rather than through `takeWhile`, since the
predicate depends on `n` and mathlib's list combinators are not parameterized in a second
argument. -/

def splitAtAdequate (n : ℕ) : List BitString → Option (List BitString × BitString × List BitString)
  | [] => none
  | σ :: L =>
      if σ.length ≤ n then some ([], σ, L)
      else (splitAtAdequate n L).map fun t ↦ (σ :: t.1, t.2.1, t.2.2)

/-- **The splitter contract.** -/
theorem splitAtAdequate_spec : ∀ {n : ℕ} {free before after : List BitString} {σ : BitString},
    splitAtAdequate n free = some (before, σ, after) →
      free = before ++ σ :: after ∧ (∀ ρ ∈ before, n < ρ.length) ∧ σ.length ≤ n := by
  intro n free
  induction free with
  | nil => intro before after σ h; rw [splitAtAdequate] at h; exact absurd h (by simp)
  | cons μ L ih =>
    intro before after σ h
    rw [splitAtAdequate] at h
    by_cases hμ : μ.length ≤ n
    · rw [if_pos hμ, Option.some_inj, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, by simp, hμ⟩
    · rw [if_neg hμ, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, hEq⟩ := h
      obtain ⟨hb, hs, ha⟩ := ih ht
      rw [Prod.mk.injEq, Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl, rfl⟩ := hEq
      refine ⟨by rw [hb]; rfl, ?_, ha⟩
      intro ρ hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · omega
      · exact hs ρ hρ'

/-- **Completeness of the splitter**: an adequate slot is found whenever one exists. -/
theorem splitAtAdequate_isSome {n : ℕ} {free : List BitString}
    (h : ∃ σ ∈ free, σ.length ≤ n) : (splitAtAdequate n free).isSome := by
  induction free with
  | nil => obtain ⟨σ, hσ, -⟩ := h; exact absurd hσ (by simp)
  | cons μ L ih =>
    rw [splitAtAdequate]
    by_cases hμ : μ.length ≤ n
    · rw [if_pos hμ]; rfl
    · rw [if_neg hμ, Option.isSome_map]
      refine ih ?_
      obtain ⟨σ, hσ, hlen⟩ := h
      rcases List.mem_cons.mp hσ with rfl | hσ'
      · exact absurd hlen hμ
      · exact ⟨σ, hσ', hlen⟩

theorem primrec_splitAtAdequate : Primrec₂ splitAtAdequate := by
  have hstep : Primrec₂ fun (z : ℕ × List BitString)
      (p : BitString × List BitString × Option (List BitString × BitString × List BitString)) ↦
      (if p.1.length ≤ z.1 then some ([], p.1, p.2.1)
        else p.2.2.map fun t ↦ (p.1 :: t.1, t.2.1, t.2.2)) := by
    refine Primrec.ite
      (Primrec.nat_le.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.option_some.comp
        (Primrec.pair (Primrec.const [])
          (Primrec.pair (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))) ?_
    refine Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) ?_
    exact (Primrec.pair
      (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  refine (Primrec.list_rec Primrec.snd
    (Primrec.const (none : Option (List BitString × BitString × List BitString)))
    hstep).of_eq fun z ↦ ?_
  obtain ⟨n, L⟩ := z
  induction L with
  | nil => rfl
  | cons μ L ih => rw [splitAtAdequate, ← ih]

/-! ## The allocator -/

/-- Incompatibility is symmetric, which is what lets the invariant's single ordered clause be
taken apart and reassembled in a different order. -/
private theorem not_compatible_symm {a b : BitString} (h : ¬BitString.Compatible a b) :
    ¬BitString.Compatible b a := fun hc ↦ h hc.symm

/-- Fulfil one request: take the longest adequate slot, descend to the requested length, and put
the freed siblings back in its place. -/
def allocStep (st : AllocationState) (r : KraftRequest) : Option AllocationState :=
  (splitAtAdequate r.length st.free).map fun t ↦
    { assigned := st.assigned ++ [⟨(descend t.2.1 (r.length - t.2.1.length)).1, r.output⟩],
      free := t.1 ++ (descend t.2.1 (r.length - t.2.1.length)).2 ++ t.2.2 }

def allocFrom (st : AllocationState) (rs : List KraftRequest) : Option AllocationState :=
  rs.foldl (fun o r ↦ o.bind fun s ↦ allocStep s r) (some st)

@[simp] theorem allocFrom_nil (st : AllocationState) : allocFrom st [] = some st := rfl

private theorem allocFoldl_none (rs : List KraftRequest) :
    rs.foldl (fun o r ↦ o.bind fun s ↦ allocStep s r) none = none := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [List.foldl_cons, Option.bind_none, ih]

theorem allocFrom_cons (st : AllocationState) (r : KraftRequest) (rs : List KraftRequest) :
    allocFrom st (r :: rs) = (allocStep st r).bind fun s ↦ allocFrom s rs := by
  have hb : ((some st).bind fun s ↦ allocStep s r) = allocStep st r := rfl
  rw [allocFrom, List.foldl_cons, hb]
  cases hs : allocStep st r with
  | none => rw [allocFoldl_none, Option.bind_none]
  | some s => rfl

/-- The empty codeword is the only slot at the start. -/
def initState : AllocationState := ⟨[], [[]]⟩

def allocate (rs : List KraftRequest) : Option AllocationState := allocFrom initState rs

/-! ## The invariant -/

/-- The four clauses. Free lengths strictly decrease; everything in play is pairwise
incompatible; assignments correspond pointwise to the processed requests in both length and
output; and processed weight plus free weight is exactly one. -/
structure AllocationState.Invariant (processed : List KraftRequest) (st : AllocationState) :
    Prop where
  /-- Free slots have strictly decreasing lengths. -/
  freeSorted : (st.free.map List.length).Pairwise (· > ·)
  /-- Allocated codewords and free slots are pairwise incompatible. -/
  incompat : ((st.assigned.map Assignment.codeword) ++ st.free).Pairwise
    fun a b ↦ ¬BitString.Compatible a b
  /-- Assignments match the processed requests pointwise. -/
  correspond : st.assigned.map (fun a ↦ (a.codeword.length, a.output))
    = processed.map fun r ↦ (r.length, r.output)
  /-- Allocated mass and free mass are exactly one. -/
  mass : totalRequestWeight processed + listWeight st.free = 1

theorem invariant_initState : AllocationState.Invariant [] initState := by
  refine ⟨by simp [initState], by simp [initState], by simp [initState], ?_⟩
  rw [initState, totalRequestWeight_nil, zero_add, listWeight_cons, listWeight_nil, add_zero,
    BitString.weight]
  norm_num

/-! ## Preservation

All four clauses in one step. The geometry never reopens after this: `allocFrom_complete` is an
ordinary induction on the remaining requests. -/

theorem allocStep_preserves {processed : List KraftRequest} {st : AllocationState}
    {r : KraftRequest} (hI : AllocationState.Invariant processed st)
    (hB : totalRequestWeight (processed ++ [r]) ≤ 1) :
    ∃ st', allocStep st r = some st' ∧ AllocationState.Invariant (processed ++ [r]) st' := by
  -- the next request still fits inside the free mass, by additive cancellation
  have hfit : r.weight ≤ listWeight st.free := by
    rw [totalRequestWeight_append, totalRequestWeight_singleton] at hB
    have := hB.trans_eq hI.mass.symm
    exact le_of_add_le_add_left this
  obtain ⟨σ, hσfree, hσlen⟩ :=
    exists_adequate_slot hI.freeSorted (by rw [← KraftRequest.weight]; exact hfit)
  obtain ⟨⟨before, σ₀, after⟩, hsplit⟩ :=
    Option.isSome_iff_exists.mp (splitAtAdequate_isSome ⟨σ, hσfree, hσlen⟩)
  obtain ⟨hfree, hbefore, hσ₀⟩ := splitAtAdequate_spec hsplit
  set k := r.length - σ₀.length with hk
  set c := (descend σ₀ k).1 with hc
  set sibs := (descend σ₀ k).2 with hsibs
  have hclen : c.length = r.length := by rw [hc, length_descend_fst]; omega
  refine ⟨_, by rw [allocStep, hsplit, Option.map_some], ?_⟩
  -- unpack the old incompatibility clause
  have hincOld := hI.incompat
  rw [hfree, List.pairwise_append, List.pairwise_append, List.pairwise_cons] at hincOld
  obtain ⟨hApw, ⟨hBpw, ⟨hσafter, hAfterpw⟩, hcross⟩, hAall⟩ := hincOld
  -- and the old ordering clause
  have hafterlen : ∀ ρ ∈ after, ρ.length < σ₀.length := by
    have := hI.freeSorted
    rw [hfree, List.map_append, List.map_cons, List.pairwise_append, List.pairwise_cons] at this
    intro ρ hρ
    exact this.2.1.1 ρ.length (List.mem_map_of_mem hρ)
  have hbeforelen : ∀ ρ ∈ before, r.length < ρ.length := hbefore
  have hsiblen : ∀ ρ ∈ sibs, σ₀.length < ρ.length ∧ ρ.length ≤ r.length := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := length_of_mem_descend_snd hρ
    exact ⟨h1, by omega⟩
  -- every new string extends the chosen slot
  have hext : ∀ ρ ∈ c :: sibs, σ₀ <+: ρ := by
    intro ρ hρ
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · exact prefix_descend_fst σ₀ k
    · exact prefix_of_mem_descend_snd hρ'
  have hcsibs : (c :: sibs).Pairwise fun a b ↦ ¬BitString.Compatible a b := pairwise_descend σ₀ k
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- free lengths still strictly decrease
    simp only [List.map_append]
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · refine List.pairwise_append.mpr ⟨?_, pairwise_length_descend_snd σ₀ k, ?_⟩
      · have hs := hI.freeSorted
        rw [hfree, List.map_append] at hs
        exact (List.pairwise_append.mp hs).1
      · rintro a ha b hb
        rw [List.mem_map] at ha hb
        obtain ⟨ρ, hρ, rfl⟩ := ha
        obtain ⟨μ, hμ, rfl⟩ := hb
        have h1 := hbeforelen ρ hρ
        have h2 := (hsiblen μ hμ).2
        omega
    · have hs := hI.freeSorted
      rw [hfree, List.map_append, List.map_cons] at hs
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2
    · rintro a ha b hb
      rw [List.mem_map] at hb
      obtain ⟨μ, hμ, rfl⟩ := hb
      have h2 := hafterlen μ hμ
      rcases List.mem_append.mp ha with ha' | ha' <;> rw [List.mem_map] at ha'
      · obtain ⟨ρ, hρ, rfl⟩ := ha'
        have h1 := hbeforelen ρ hρ
        have h3 := hσ₀
        omega
      · obtain ⟨ρ, hρ, rfl⟩ := ha'
        have h1 := (hsiblen ρ hρ).1
        omega
  · -- pairwise incompatibility, reassembled
    have hAσ : ∀ a ∈ st.assigned.map Assignment.codeword, ¬BitString.Compatible a σ₀ :=
      fun a ha ↦ hAall a ha σ₀ (List.mem_append.mpr (Or.inr List.mem_cons_self))
    have hAbefore : ∀ a ∈ st.assigned.map Assignment.codeword, ∀ b ∈ before,
        ¬BitString.Compatible a b := fun a ha b hb ↦
      hAall a ha b (List.mem_append.mpr (Or.inl hb))
    have hAafter : ∀ a ∈ st.assigned.map Assignment.codeword, ∀ b ∈ after,
        ¬BitString.Compatible a b := fun a ha b hb ↦
      hAall a ha b (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hb)))
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · refine List.pairwise_append.mpr ⟨hApw, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact incompatible_of_prefix_right (hext _ List.mem_cons_self) (hAσ a ha)
    · refine List.pairwise_append.mpr ⟨?_, hAfterpw, ?_⟩
      · refine List.pairwise_append.mpr ⟨hBpw, (List.pairwise_cons.mp hcsibs).2, ?_⟩
        intro a ha b hb
        exact incompatible_of_prefix_right (hext b (List.mem_cons_of_mem _ hb))
          (hcross a ha σ₀ List.mem_cons_self)
      · intro a ha b hb
        rcases List.mem_append.mp ha with ha' | ha'
        · exact hcross a ha' b (List.mem_cons_of_mem _ hb)
        · exact not_compatible_symm (incompatible_of_prefix_right
            (hext a (List.mem_cons_of_mem _ ha')) (not_compatible_symm (hσafter b hb)))
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha' | ha'
      · rcases List.mem_append.mp hb with hb' | hb'
        · rcases List.mem_append.mp hb' with hb'' | hb''
          · exact hAbefore a ha' b hb''
          · exact incompatible_of_prefix_right (hext b (List.mem_cons_of_mem _ hb'')) (hAσ a ha')
        · exact hAafter a ha' b hb'
      · rw [List.mem_singleton] at ha'
        subst ha'
        rcases List.mem_append.mp hb with hb' | hb'
        · rcases List.mem_append.mp hb' with hb'' | hb''
          · exact not_compatible_symm (incompatible_of_prefix_right
              (hext _ List.mem_cons_self) (hcross b hb'' σ₀ List.mem_cons_self))
          · exact (List.pairwise_cons.mp hcsibs).1 b hb''
        · exact not_compatible_symm (incompatible_of_prefix_right
            (hext _ List.mem_cons_self) (not_compatible_symm (hσafter b hb')))
  · -- pointwise correspondence
    have hcorr := hI.correspond
    have hcl : (descend σ₀ (r.length - List.length σ₀)).1.length = r.length := by
      rw [length_descend_fst]; omega
    simp only [List.map_append, List.map_cons, List.map_nil, hcorr, hcl]
  · -- mass
    have hsplitw : listWeight st.free = listWeight before + r.weight + listWeight sibs
        + listWeight after := by
      rw [hfree, listWeight_append, listWeight_cons, weight_descend σ₀ k, ← hc, ← hsibs,
        KraftRequest.weight, ← hclen, BitString.weight]
      ring
    rw [totalRequestWeight_append, totalRequestWeight_singleton, listWeight_append,
      listWeight_append, ← hI.mass, hsplitw]
    ring

theorem allocFrom_complete : ∀ {remaining processed : List KraftRequest} {st : AllocationState},
    AllocationState.Invariant processed st → totalRequestWeight (processed ++ remaining) ≤ 1 →
    ∃ st', allocFrom st remaining = some st' ∧
      AllocationState.Invariant (processed ++ remaining) st' := by
  intro remaining
  induction remaining with
  | nil => intro processed st hI hB; exact ⟨st, rfl, by rwa [List.append_nil]⟩
  | cons r rs ih =>
    intro processed st hI hB
    have hstep : totalRequestWeight (processed ++ [r]) ≤ 1 := by
      refine le_trans ?_ hB
      rw [totalRequestWeight_append, totalRequestWeight_append, totalRequestWeight_singleton]
      refine add_le_add le_rfl ?_
      simp only [totalRequestWeight, List.map_cons, List.sum_cons]
      exact le_self_add
    obtain ⟨st₁, hst₁, hI₁⟩ := allocStep_preserves hI hstep
    have hB₁ : totalRequestWeight ((processed ++ [r]) ++ rs) ≤ 1 := by
      rwa [List.append_assoc, List.singleton_append]
    obtain ⟨st', hst', hI'⟩ := ih hI₁ hB₁
    refine ⟨st', by rw [allocFrom_cons, hst₁]; exact hst', ?_⟩
    rwa [List.append_assoc, List.singleton_append] at hI'

/-- **The allocator is complete.** Any request list inside the Kraft budget is fully allocated,
and the resulting state satisfies the invariant. -/
theorem allocate_complete {rs : List KraftRequest} (h : totalRequestWeight rs ≤ 1) :
    ∃ st, allocate rs = some st ∧ AllocationState.Invariant rs st := by
  obtain ⟨st, hst, hI⟩ := allocFrom_complete invariant_initState (by rwa [List.nil_append])
  exact ⟨st, hst, by rwa [List.nil_append] at hI⟩

/-! ## Computability of the allocator -/

theorem primrec_allocStep : Primrec₂ allocStep := by
  have hsplit : Primrec fun z : AllocationState × KraftRequest ↦
      splitAtAdequate z.2.length z.1.free :=
    primrec_splitAtAdequate.comp (primrec_kraftRequest_length.comp Primrec.snd)
      (primrec_allocationState_free.comp Primrec.fst)
  have hdesc : Primrec fun w : (AllocationState × KraftRequest) ×
      (List BitString × BitString × List BitString) ↦
      descend w.2.2.1 (w.1.2.length - w.2.2.1.length) :=
    primrec_descend.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_sub.comp
        (primrec_kraftRequest_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hbody : Primrec₂ fun (z : AllocationState × KraftRequest)
      (t : List BitString × BitString × List BitString) ↦
      AllocationState.mk
        (z.1.assigned ++ [Assignment.mk (descend t.2.1 (z.2.length - t.2.1.length)).1 z.2.output])
        (t.1 ++ (descend t.2.1 (z.2.length - t.2.1.length)).2 ++ t.2.2) := by
    have hassigned : Primrec fun w : (AllocationState × KraftRequest) ×
        (List BitString × BitString × List BitString) ↦
        w.1.1.assigned ++ [Assignment.mk (descend w.2.2.1 (w.1.2.length - w.2.2.1.length)).1
          w.1.2.output] := by
      refine Primrec.list_append.comp
        ((primrec_allocationState_assigned.comp Primrec.fst).comp Primrec.fst) ?_
      refine Primrec.list_cons.comp ?_ (Primrec.const [])
      exact (Primrec.of_equiv_symm_iff (e := Assignment.equivProd) |>.mpr
        (Primrec.pair (Primrec.fst.comp hdesc)
          (primrec_kraftRequest_output.comp (Primrec.snd.comp Primrec.fst)))).of_eq fun _ ↦ rfl
    have hfreeNew : Primrec fun w : (AllocationState × KraftRequest) ×
        (List BitString × BitString × List BitString) ↦
        w.2.1 ++ (descend w.2.2.1 (w.1.2.length - w.2.2.1.length)).2 ++ w.2.2.2 :=
      Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp hdesc))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact (Primrec.of_equiv_symm_iff (e := AllocationState.equivProd) |>.mpr
      (Primrec.pair hassigned hfreeNew)).of_eq fun _ ↦ rfl
  exact Primrec.option_map hsplit hbody

theorem primrec_allocFrom : Primrec₂ allocFrom := by
  have hstep : Primrec₂ fun (z : AllocationState × List KraftRequest)
      (p : Option AllocationState × KraftRequest) ↦ p.1.bind fun s ↦ allocStep s p.2 := by
    refine Primrec.option_bind (Primrec.fst.comp Primrec.snd) ?_
    exact (primrec_allocStep.comp Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.list_foldl Primrec.snd
    (Primrec.option_some.comp Primrec.fst) hstep

theorem primrec_allocate : Primrec allocate :=
  primrec_allocFrom.comp (Primrec.const initState) Primrec.id

/-! ## Prefix stability of the allocation

Allocation is a deterministic fold and `allocStep` only ever appends one assignment, so growing
the request list can only extend the assignment list. That is what makes the eventual machine's
lookup stable, and it replaces what would otherwise be a combinatorial argument about the machine
domain. -/

private theorem someBind {α β : Type} (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

theorem allocFrom_append (st : AllocationState) (rs ss : List KraftRequest) :
    allocFrom st (rs ++ ss) = (allocFrom st rs).bind fun s ↦ allocFrom s ss := by
  induction rs generalizing st with
  | nil => rw [List.nil_append, allocFrom_nil, someBind]
  | cons r rs ih =>
    rw [List.cons_append, allocFrom_cons, allocFrom_cons]
    cases h : allocStep st r with
    | none => simp [Option.bind_none]
    | some s' => rw [someBind, someBind, ih]

theorem assigned_prefix_allocStep {st st' : AllocationState} {r : KraftRequest}
    (h : allocStep st r = some st') : st.assigned <+: st'.assigned := by
  rw [allocStep, Option.map_eq_some_iff] at h
  obtain ⟨t, -, rfl⟩ := h
  exact ⟨_, rfl⟩

theorem assigned_prefix_allocFrom : ∀ {rs : List KraftRequest} {st st' : AllocationState},
    allocFrom st rs = some st' → st.assigned <+: st'.assigned := by
  intro rs
  induction rs with
  | nil => intro st st' h; rw [allocFrom_nil, Option.some_inj] at h; rw [h]
  | cons r rs ih =>
    intro st st' h
    rw [allocFrom_cons] at h
    cases hs : allocStep st r with
    | none => rw [hs, Option.bind_none] at h; exact absurd h (by simp)
    | some s' =>
      rw [hs, someBind] at h
      exact (assigned_prefix_allocStep hs).trans (ih h)

theorem allocate_append (rs ss : List KraftRequest) :
    allocate (rs ++ ss) = (allocate rs).bind fun s ↦ allocFrom s ss :=
  allocFrom_append initState rs ss

/-! ## Request traces -/

/-- A computably enumerable, append-only stream of requests staying inside the Kraft budget. -/
structure KraftRequestTrace where
  /-- The cumulative request list at each stage. -/
  stage : ℕ → List KraftRequest
  /-- Requests are only ever appended. -/
  stage_prefix : ∀ {s t : ℕ}, s ≤ t → stage s <+: stage t
  /-- The stream is computable. -/
  primrec_stage : Primrec stage
  /-- Every stage stays inside the budget. -/
  weight_le : ∀ s, totalRequestWeight (stage s) ≤ 1

namespace KraftRequestTrace

variable (R : KraftRequestTrace)

/-- The allocator state after stage `s`. The default is unreachable, by `allocate_stage`. -/
def allocStage (s : ℕ) : AllocationState := (allocate (R.stage s)).getD initState

theorem allocate_stage (s : ℕ) : allocate (R.stage s) = some (R.allocStage s) := by
  obtain ⟨st, hst, -⟩ := allocate_complete (R.weight_le s)
  rw [allocStage, hst, Option.getD_some]

theorem invariant_allocStage (s : ℕ) :
    AllocationState.Invariant (R.stage s) (R.allocStage s) := by
  obtain ⟨st, hst, hI⟩ := allocate_complete (R.weight_le s)
  have heq : R.allocStage s = st := by rw [allocStage, hst, Option.getD_some]
  rw [heq]
  exact hI

/-- The assignments in force at stage `s`. -/
def assignmentsStage (s : ℕ) : List Assignment := (R.allocStage s).assigned

variable {R}

/-- **Assignment-prefix stability.** -/
theorem assignmentsStage_prefix {s t : ℕ} (hst : s ≤ t) :
    R.assignmentsStage s <+: R.assignmentsStage t := by
  obtain ⟨l, hl⟩ := R.stage_prefix hst
  have hA : allocate (R.stage t) = allocFrom (R.allocStage s) l := by
    rw [← hl, allocate_append, allocate_stage R s, someBind]
  rw [allocate_stage R t] at hA
  exact assigned_prefix_allocFrom hA.symm

/-- Codewords in force at a stage are distinct, since incompatibility is irreflexive. -/
theorem nodup_codewords (R : KraftRequestTrace) (s : ℕ) :
    ((R.assignmentsStage s).map Assignment.codeword).Nodup := by
  have h := (R.invariant_allocStage s).incompat
  rw [List.pairwise_append] at h
  refine List.Pairwise.imp ?_ h.1
  intro a b hab heq
  subst heq
  exact hab (Or.inl (List.prefix_refl a))

end KraftRequestTrace

/-! ## Assignment lookup

A fold rather than `List.find`, whose mathlib API is not parameterized in the sought value. The
leftmost match wins, which is what makes lookup stable under extension. -/

def lookupAssignment (p : BitString) (A : List Assignment) : Option BitString :=
  A.foldr (fun a acc ↦ if a.codeword = p then some a.output else acc) none

@[simp] theorem lookupAssignment_nil (p : BitString) : lookupAssignment p [] = none := rfl

theorem lookupAssignment_cons (p : BitString) (a : Assignment) (A : List Assignment) :
    lookupAssignment p (a :: A)
      = if a.codeword = p then some a.output else lookupAssignment p A := rfl

theorem exists_of_lookupAssignment : ∀ {A : List Assignment} {p τ : BitString},
    lookupAssignment p A = some τ → ∃ a ∈ A, a.codeword = p ∧ a.output = τ := by
  intro A
  induction A with
  | nil => intro p τ h; rw [lookupAssignment_nil] at h; exact absurd h (by simp)
  | cons a A ih =>
    intro p τ h
    rw [lookupAssignment_cons] at h
    by_cases hc : a.codeword = p
    · rw [if_pos hc, Option.some_inj] at h
      exact ⟨a, List.mem_cons_self, hc, h⟩
    · rw [if_neg hc] at h
      obtain ⟨b, hb, hbc, hbo⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem a hb, hbc, hbo⟩

/-- A fold that has already succeeded ignores its starting value. -/
private theorem lookupFoldr_of_eq_some : ∀ {A : List Assignment} {p τ : BitString}
    (x : Option BitString), lookupAssignment p A = some τ →
    A.foldr (fun a acc ↦ if a.codeword = p then some a.output else acc) x = some τ := by
  intro A
  induction A with
  | nil => intro p τ x h; rw [lookupAssignment_nil] at h; exact absurd h (by simp)
  | cons a A ih =>
    intro p τ x h
    rw [lookupAssignment_cons] at h
    by_cases hc : a.codeword = p
    · rw [List.foldr_cons, if_pos hc]; rwa [if_pos hc] at h
    · rw [List.foldr_cons, if_neg hc]; rw [if_neg hc] at h; exact ih x h

/-- **Lookup is stable under extension.** -/
theorem lookupAssignment_prefix {p τ : BitString} {A B : List Assignment} (h : A <+: B)
    (hA : lookupAssignment p A = some τ) : lookupAssignment p B = some τ := by
  obtain ⟨l, rfl⟩ := h
  rw [lookupAssignment, List.foldr_append]
  exact lookupFoldr_of_eq_some _ hA

/-- With distinct codewords, lookup returns the assignment's own output. -/
theorem lookupAssignment_of_mem : ∀ {A : List Assignment} {a : Assignment}, a ∈ A →
    (A.map Assignment.codeword).Nodup → lookupAssignment a.codeword A = some a.output := by
  intro A
  induction A with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons b A ih =>
    intro a ha hnd
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [lookupAssignment_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [if_pos rfl]
    · by_cases hc : b.codeword = a.codeword
      · exact absurd (hc ▸ List.mem_map_of_mem ha') hnd.1
      · rw [if_neg hc]; exact ih ha' hnd.2

theorem primrec_lookupAssignment : Primrec₂ lookupAssignment := by
  have hstep : Primrec₂ fun (p : BitString × List Assignment) (q : Assignment × Option BitString) ↦
      (if q.1.codeword = p.1 then some q.1.output else q.2) := by
    refine Primrec.ite
      (Primrec.eq.comp (primrec_assignment_codeword.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.option_some.comp (primrec_assignment_output.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd (Primrec.const none) hstep

/-- Symmetric extraction from a pairwise list, since `List.Pairwise.forall` wants a `Std.Symm`
instance rather than a symmetry proof. -/
private theorem pairwise_incompat_pair : ∀ {l : List BitString},
    (l.Pairwise fun a b ↦ ¬BitString.Compatible a b) → ∀ {a b : BitString}, a ∈ l → b ∈ l →
    a ≠ b → ¬BitString.Compatible a b := by
  intro l
  induction l with
  | nil => intro _ a b ha; exact absurd ha (by simp)
  | cons c l ih =>
    intro h a b ha hb hne
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hne
    · exact h.1 b hb'
    · exact not_compatible_symm (h.1 a ha')
    · exact ih h.2 ha' hb' hne

/-! ## The machine

Search for a stage at which the input has been assigned, then emit the stored output. Prefix
stability makes the answer independent of which stage is found, so the least one — which is what
`Nat.rfind` returns — is as good as any. -/

namespace KraftRequestTrace

variable (R : KraftRequestTrace)

theorem primrec_assignmentsStage : Primrec R.assignmentsStage :=
  primrec_allocationState_assigned.comp
    (Primrec.option_getD.comp (primrec_allocate.comp R.primrec_stage) (Primrec.const initState))

noncomputable def machineEval (m : ℕ) : Part ℕ :=
  (Part.ofOption (canonicalBitString m)).bind fun p ↦
    (Nat.rfind fun s ↦ Part.some ((lookupAssignment p (R.assignmentsStage s)).isSome)).map
      fun s ↦ Encodable.encode ((lookupAssignment p (R.assignmentsStage s)).getD [])

theorem partrec_machineEval : Nat.Partrec R.machineEval := by
  have hlook : Primrec fun w : (ℕ × BitString) × ℕ ↦
      lookupAssignment w.1.2 (R.assignmentsStage w.2) :=
    primrec_lookupAssignment.comp (Primrec.snd.comp Primrec.fst)
      (R.primrec_assignmentsStage.comp Primrec.snd)
  refine Partrec.nat_iff.mp (Partrec.bind (Computable.ofOption ?_) ?_)
  · exact primrec_canonicalBitString.to_comp
  · refine Partrec.map (Partrec.rfind ?_) ?_
    · exact Computable₂.partrec₂
        (Computable.to₂ (Primrec.option_isSome.comp hlook).to_comp)
    · exact (Primrec.encode.comp (Primrec.option_getD.comp hlook (Primrec.const []))).to_comp.to₂

noncomputable def machineCode : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.mp R.partrec_machineEval).choose

theorem eval_machineCode : R.machineCode.eval = R.machineEval :=
  (Nat.Partrec.Code.exists_code.mp R.partrec_machineEval).choose_spec

/-- **The semantic seam.** Everything below is derived from this. -/
theorem describes_machineCode_iff (p τ : BitString) :
    PrefixMachine.Describes R.machineCode p τ ↔
      ∃ s, ∃ a ∈ R.assignmentsStage s, a.codeword = p ∧ a.output = τ := by
  rw [PrefixMachine.Describes, eval_machineCode, machineEval, canonicalBitString_encode]
  constructor
  · intro h
    rw [Part.coe_some, Part.bind_some, Part.eq_some_iff, Part.mem_map_iff] at h
    obtain ⟨s, hs, henc⟩ := h
    have hsome : (lookupAssignment p (R.assignmentsStage s)).isSome := by
      simpa using Nat.rfind_spec hs
    obtain ⟨υ, hυ⟩ := Option.isSome_iff_exists.mp hsome
    rw [hυ, Option.getD_some] at henc
    obtain ⟨a, ha, hac, hao⟩ := exists_of_lookupAssignment hυ
    exact ⟨s, a, ha, hac, hao.trans (Encodable.encode_injective henc)⟩
  · rintro ⟨s, a, ha, rfl, rfl⟩
    have hlook : lookupAssignment a.codeword (R.assignmentsStage s) = some a.output :=
      lookupAssignment_of_mem ha (R.nodup_codewords s)
    obtain ⟨n, hn, -⟩ := Nat.rfind_min'
      (p := fun t ↦ (lookupAssignment a.codeword (R.assignmentsStage t)).isSome)
      (by rw [hlook]; rfl)
    have hsome : (lookupAssignment a.codeword (R.assignmentsStage n)).isSome := by
      simpa using Nat.rfind_spec hn
    obtain ⟨υ, hυ⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨b, hb, hbc, hbo⟩ := exists_of_lookupAssignment hυ
    have hstable : lookupAssignment a.codeword (R.assignmentsStage (max s n)) = some a.output :=
      lookupAssignment_prefix (assignmentsStage_prefix (le_max_left s n)) hlook
    have hstable' : lookupAssignment a.codeword (R.assignmentsStage (max s n)) = some υ :=
      lookupAssignment_prefix (assignmentsStage_prefix (le_max_right s n)) hυ
    have hυa : υ = a.output := by
      rw [hstable] at hstable'
      exact (Option.some_inj.mp hstable').symm
    rw [Part.coe_some, Part.bind_some, Part.eq_some_iff, Part.mem_map_iff]
    exact ⟨n, hn, by rw [hυ, Option.getD_some, hυa]⟩

theorem mem_machineDomain_machineCode_iff (p : BitString) :
    p ∈ PrefixMachine.machineDomain R.machineCode ↔
      ∃ s, ∃ a ∈ R.assignmentsStage s, a.codeword = p := by
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    rw [eval_machineCode, machineEval, canonicalBitString_encode, Part.coe_some, Part.bind_some,
      Part.mem_map_iff] at hx
    obtain ⟨s, hs, -⟩ := hx
    have hsome : (lookupAssignment p (R.assignmentsStage s)).isSome := by
      simpa using Nat.rfind_spec hs
    obtain ⟨υ, hυ⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨a, ha, hac, -⟩ := exists_of_lookupAssignment hυ
    exact ⟨s, a, ha, hac⟩
  · rintro ⟨s, a, ha, rfl⟩
    exact ((describes_machineCode_iff R a.codeword a.output).mpr
      ⟨s, a, ha, rfl, rfl⟩).mem_machineDomain

/-- **Prefix-freeness**: two assigned codewords coexist at the later stage, where the allocation
invariant puts them in one pairwise-incompatible list. -/
theorem isPrefixFreeMachine_machineCode :
    PrefixMachine.IsPrefixFreeMachine R.machineCode := by
  rw [PrefixMachine.IsPrefixFreeMachine, prefixFree_iff]
  intro p hp q hq hpre
  obtain ⟨s, a, ha, rfl⟩ := (mem_machineDomain_machineCode_iff R _).mp hp
  obtain ⟨t, b, hb, rfl⟩ := (mem_machineDomain_machineCode_iff R _).mp hq
  have ha' : a ∈ R.assignmentsStage (max s t) :=
    (assignmentsStage_prefix (le_max_left s t)).subset ha
  have hb' : b ∈ R.assignmentsStage (max s t) :=
    (assignmentsStage_prefix (le_max_right s t)).subset hb
  by_contra hne
  have hinc := (R.invariant_allocStage (max s t)).incompat
  rw [List.pairwise_append] at hinc
  exact pairwise_incompat_pair hinc.1 (List.mem_map_of_mem ha') (List.mem_map_of_mem hb') hne
    (Or.inl hpre)

noncomputable def machine : PrefixFreeMachine :=
  ⟨R.machineCode, R.isPrefixFreeMachine_machineCode⟩

/-- **The acceptance theorem.** Every request appearing at some stage is realized by a codeword of
exactly its requested length. -/
theorem request_described {r : KraftRequest} {s : ℕ} (h : r ∈ R.stage s) :
    ∃ p, p.length = r.length ∧ PrefixMachine.Describes R.machine.program p r.output := by
  have hcorr := (R.invariant_allocStage s).correspond
  have hmem : (r.length, r.output) ∈ (R.assignmentsStage s).map
      fun a ↦ (a.codeword.length, a.output) := by
    rw [assignmentsStage, hcorr]
    exact List.mem_map_of_mem h
  rw [List.mem_map] at hmem
  obtain ⟨a, ha, hEq⟩ := hmem
  rw [Prod.mk.injEq] at hEq
  exact ⟨a.codeword, hEq.1, (describes_machineCode_iff R a.codeword r.output).mpr
    ⟨s, a, ha, rfl, hEq.2⟩⟩

end KraftRequestTrace

/-! ## Executable check

Lengths `3, 2, 1` total `7/8`, so allocation must succeed. This is the exact pattern the
shortest-adequate-slot rule fails on: after the length-3 request the free lengths are `3, 2, 1`,
and serving the length-2 request from the length-1 slot would duplicate length `2` and leave
nothing for the length-1 request. -/

section Examples

set_option linter.hashCommand false

/-- The regression example: three requests whose weights sum to `7/8`. -/
def exampleRequests : List KraftRequest :=
  [⟨3, [true]⟩, ⟨2, [false]⟩, ⟨1, [true, true]⟩]

#guard (allocate exampleRequests).isSome

#guard ((allocate exampleRequests).getD initState).assigned.length = 3

-- each codeword has exactly its requested length
#guard (((allocate exampleRequests).getD initState).assigned.map
  fun a ↦ a.codeword.length) = [3, 2, 1]

end Examples

end AlgorithmicRandomness
