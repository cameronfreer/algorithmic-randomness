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

end AlgorithmicRandomness
