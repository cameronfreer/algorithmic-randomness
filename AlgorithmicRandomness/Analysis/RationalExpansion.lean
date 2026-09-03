/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.AffineDyadic
import AlgorithmicRandomness.Analysis.LipschitzRandomness
import AlgorithmicRandomness.Randomness.Kurtz

/-!
# A computably random real is irrational

The expansions of a rational `r` are exactly the paths of the tree of strings whose dyadic interval
contains `r`. That tree is *decidable* — membership is two comparisons of coded rationals — and its
path class is null, because at most two intervals of a given level can contain a point. So the
expansions of a rational form a null effectively closed class, which Kurtz randomness already
forbids.

This is much cheaper than the direct route. Producing the expansions themselves would need a greedy
bisection program, a case analysis at dyadic boundaries where two expansions exist, and a proof
that the non-greedy one is eventually constant. None of that is needed: the tree is definable
without naming its paths, and the counting bound replaces the boundary analysis.

The consequence is what the affine transport needs. A computably random real is irrational, so
`(z - q) / p` is irrational for rational `p ≠ 0` and `q`, and an irrational point of the unit
interval has a *unique* binary expansion — which is what turns success on one expansion into a
refutation of the existential `IsComputablyRandomReal`.

Irrationality is stated as `∀ r : ℚ, z ≠ r` rather than through mathlib's `Irrational`, which is
definitionally the same but would pull in a module the pinned build does not otherwise need.
-/

open MeasureTheory

open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-! ## The identity grid

The coded dyadic endpoints are the affine ones at scale `1` and shift `0`, so the fold and its
correctness proof are reused rather than repeated. -/

/-- The affine grid that is the plain dyadic grid. -/
def dyadicGrid : AffineDyadicGrid where
  scaleCode := NNRatCode.ofNat 1
  shiftCode := RatCode.ofNat 0
  scale_pos := by rw [NNRatCode.value_ofNat]; norm_num

@[simp] theorem scale_dyadicGrid : dyadicGrid.scale = 1 := by
  rw [AffineDyadicGrid.scale, dyadicGrid, NNRatCode.value_ofNat]
  norm_num

@[simp] theorem shift_dyadicGrid : dyadicGrid.shift = 0 := by
  rw [AffineDyadicGrid.shift, dyadicGrid, RatCode.value_ofNat]
  norm_num

@[simp] theorem left_dyadicGrid (σ : BitString) : dyadicGrid.left σ = dyadicLeft σ := by
  rw [AffineDyadicGrid.left, scale_dyadicGrid, shift_dyadicGrid]
  ring

@[simp] theorem right_dyadicGrid (σ : BitString) : dyadicGrid.right σ = dyadicRight σ := by
  rw [AffineDyadicGrid.right, AffineDyadicGrid.width, left_dyadicGrid, scale_dyadicGrid,
    dyadicRight]
  ring

/-! ## The tree of intervals containing a rational -/

/-- Membership: the coded left endpoint is at most `rc`, and `rc` is at most the coded right
endpoint. Both are comparisons of coded rationals. -/
def rationalMember (rc : ℕ) (σ : BitString) : Bool :=
  RatCode.le (dyadicGrid.leftCode σ) rc && RatCode.le rc (dyadicGrid.rightCode σ)

theorem rationalMember_eq_true_iff {rc : ℕ} {σ : BitString} :
    rationalMember rc σ = true ↔ ((RatCode.value rc : ℚ) : ℝ) ∈ dyadicInterval σ := by
  rw [rationalMember, Bool.and_eq_true, RatCode.le_iff, RatCode.le_iff, dyadicInterval,
    Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← left_dyadicGrid, ← dyadicGrid.value_leftCode σ]
      exact_mod_cast h1
    · rw [← right_dyadicGrid, ← dyadicGrid.value_rightCode σ]
      exact_mod_cast h2
  · rintro ⟨h1, h2⟩
    rw [← left_dyadicGrid, ← dyadicGrid.value_leftCode σ] at h1
    rw [← right_dyadicGrid, ← dyadicGrid.value_rightCode σ] at h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem computable_rationalMember (rc : ℕ) : Computable (rationalMember rc) := by
  have hle : Primrec fun σ : BitString ↦ RatCode.le (dyadicGrid.leftCode σ) rc :=
    RatCode.primrec_le.comp dyadicGrid.primrec_leftCode (Primrec.const rc)
  have hre : Primrec fun σ : BitString ↦ RatCode.le rc (dyadicGrid.rightCode σ) :=
    RatCode.primrec_le.comp (Primrec.const rc) dyadicGrid.primrec_rightCode
  exact (Primrec.and.comp hle hre).to_comp

private theorem computable_rationalMemberFun (rc : ℕ) : Computable fun m : ℕ ↦
    Encodable.encode (rationalMember rc ((Encodable.decode (α := BitString) m).getD [])) :=
  Computable.encode.comp ((computable_rationalMember rc).comp
    (Primrec.option_getD.comp Primrec.decode (Primrec.const [])).to_comp)

/-- **The tree of expansions of a coded rational.** -/
noncomputable def rationalTree (rc : ℕ) : ComputableTree where
  nodes := {σ | ((RatCode.value rc : ℚ) : ℝ) ∈ dyadicInterval σ}
  prefix_closed hσ hτ := dyadicInterval_subset_of_prefix hτ hσ
  member := rationalMember rc
  member_iff _ := rationalMember_eq_true_iff
  program := NatFunctionCode.ofComputable (computable_rationalMemberFun rc)
  eval_member σ := by
    rw [NatFunctionCode.ofComputable_toFun, Encodable.encodek, Option.getD_some]

/-- Its paths are exactly the expansions of the rational. -/
theorem mem_paths_rationalTree_iff {rc : ℕ} {x : Cantor} :
    x ∈ (rationalTree rc).paths ↔ realOf x = ((RatCode.value rc : ℚ) : ℝ) := by
  constructor
  · intro hx
    exact (eq_realOf_of_mem_all_dyadicInterval fun n ↦ hx n).symm
  · intro hx n
    have hmem : realOf x ∈ dyadicInterval (initSeg x n) := realOf_mem_dyadicInterval x n
    rw [hx] at hmem
    exact hmem

/-! ## The path class is null

At most two dyadic intervals of a level contain a point, so the level fronts have at most two
members and the level weights are `2 · 2⁻ⁿ`. -/

theorem length_levelFront_rationalTree_le (rc n : ℕ) :
    ((rationalTree rc).levelFront n).length ≤ 2 := by
  set r : ℝ := ((RatCode.value rc : ℚ) : ℝ) with hr
  set J : ℕ := ⌊(2 : ℝ) ^ n * r⌋₊ with hJ
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hsub : (rationalTree rc).levelFront n ⊆
      [(BitString.wordsOfLength n).getD (J - 1) [], (BitString.wordsOfLength n).getD J []] := by
    intro σ hσ
    obtain ⟨hlen, hmem⟩ := ComputableTree.mem_levelFront_iff.mp hσ
    have hmem' : r ∈ dyadicInterval σ := hmem
    rw [dyadicInterval, Set.mem_Icc, dyadicLeft_eq_gridPoint, dyadicRight_eq_gridPoint_succ,
      gridPoint, gridPoint, hlen] at hmem'
    obtain ⟨h1, h2⟩ := hmem'
    rw [div_le_iff₀ hpow] at h1
    rw [le_div_iff₀ hpow] at h2
    have hle : gridIndex σ ≤ J := by
      rw [hJ]
      refine Nat.le_floor ?_
      linarith
    have h2' : (2 : ℝ) ^ n * r ≤ ((gridIndex σ + 1 : ℕ) : ℝ) := by
      push_cast at h2 ⊢
      linarith
    have hge : J ≤ gridIndex σ + 1 := Nat.floor_le_of_le h2'
    have hσeq : (BitString.wordsOfLength n).getD (gridIndex σ) [] = σ := by
      rw [← hlen]
      exact getD_wordsOfLength_gridIndex σ
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · rw [← hσeq, heq]
      simp
    · have : gridIndex σ = J - 1 := by omega
      rw [← hσeq, this]
      simp
  have hnd := ComputableTree.nodup_levelFront (rationalTree rc) n
  have hcard : ((rationalTree rc).levelFront n).toFinset.card
      ≤ ([(BitString.wordsOfLength n).getD (J - 1) [],
          (BitString.wordsOfLength n).getD J []] : List BitString).toFinset.card := by
    refine Finset.card_le_card fun σ hσ ↦ ?_
    exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hσ))
  rw [List.toFinset_card_of_nodup hnd] at hcard
  refine le_trans hcard (le_trans (List.toFinset_card_le _) ?_)
  simp

theorem levelWeight_rationalTree_le (rc n : ℕ) :
    (rationalTree rc).levelWeight n ≤ 2 * (2⁻¹ : ℚ≥0) ^ n := by
  rw [ComputableTree.levelWeight, ComputableTree.survivorCount_eq_length]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast length_levelFront_rationalTree_le rc n

theorem fairCoin_paths_rationalTree (rc : ℕ) : fairCoin (rationalTree rc).paths = 0 := by
  have htend : Filter.Tendsto (fun n : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ n) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  refine le_antisymm (ge_of_tendsto' htend fun n ↦ ?_) zero_le
  have hsub : (rationalTree rc).paths ⊆ (rationalTree rc).levelCover (n + 1) := by
    rw [ComputableTree.paths_eq_iInter_levelCover]
    exact Set.iInter_subset _ (n + 1)
  refine le_trans (measure_mono hsub) ?_
  rw [ComputableTree.fairCoin_levelCover, ← coe_pow_inv_two, coe_le_coe_nnrat]
  refine le_trans (levelWeight_rationalTree_le rc (n + 1)) (le_of_eq ?_)
  rw [pow_succ]
  ring

/-! ## The consequence -/

/-- Every rational is coded. -/
theorem RatCode.value_surjective (r : ℚ) : ∃ m, RatCode.value m = r := by
  rcases le_total 0 r with h | h
  · obtain ⟨a, ha⟩ := NNRatCode.value_surjective r.toNNRat
    refine ⟨RatCode.ofNNRat a, ?_⟩
    rw [RatCode.value_ofNNRat, ha]
    exact_mod_cast Rat.coe_toNNRat r h
  · obtain ⟨a, ha⟩ := NNRatCode.value_surjective (-r).toNNRat
    refine ⟨RatCode.neg (RatCode.ofNNRat a), ?_⟩
    rw [RatCode.value_neg, RatCode.value_ofNNRat, ha]
    have : ((-r).toNNRat : ℚ) = -r := by
      exact_mod_cast Rat.coe_toNNRat (-r) (by linarith)
    rw [this, neg_neg]

/-- **No expansion of a rational is Kurtz random.** -/
theorem not_isKurtzRandom_of_realOf_rat {x : Cantor} {r : ℚ} (h : realOf x = (r : ℝ)) :
    ¬IsKurtzRandom x := by
  obtain ⟨rc, hrc⟩ := RatCode.value_surjective r
  refine not_isKurtzRandom_of_mem_paths (fairCoin_paths_rationalTree rc) ?_
  rw [mem_paths_rationalTree_iff, hrc]
  exact h

/-- **A computably random real is irrational.** -/
theorem IsComputablyRandomReal.ne_rat {z : ℝ} (h : IsComputablyRandomReal z) (r : ℚ) :
    z ≠ (r : ℝ) := by
  obtain ⟨x, hx, hrand⟩ := h
  intro hz
  exact not_isKurtzRandom_of_realOf_rat (r := r) (by rw [hx, hz]) hrand.isKurtzRandom

theorem not_isComputablyRandomReal_rat (r : ℚ) : ¬IsComputablyRandomReal (r : ℝ) :=
  fun h ↦ h.ne_rat r rfl

/-! ## Bit changes along a non-rational expansion

A point whose value is not rational cannot have an eventually constant expansion, so its bits
change infinitely often; and at a change the point sits in the middle half of the cell it is in.
Both are what the affine geometry consumes: the changed bits are `n` and `n + 1`, while the
containing cell is `initSeg x n`. -/

private theorem eq_of_no_bit_change {x : Cantor} {N : ℕ} (h : ∀ n, N ≤ n → x n = x (n + 1)) :
    ∀ n, N ≤ n → x n = x N := by
  refine Nat.le_induction rfl ?_
  intro n hn ih
  rw [← h n hn, ih]

private theorem dyadicLeft_initSeg_eq_of_false {x : Cantor} {N : ℕ}
    (hb : ∀ n, N ≤ n → x n = false) :
    ∀ m, N ≤ m → dyadicLeft (initSeg x m) = dyadicLeft (initSeg x N) := by
  refine Nat.le_induction rfl ?_
  intro m hm ih
  rw [initSeg_succ, hb m hm, dyadicLeft_append_false, ih]

private theorem dyadicRight_initSeg_eq_of_true {x : Cantor} {N : ℕ}
    (hb : ∀ n, N ≤ n → x n = true) :
    ∀ m, N ≤ m → dyadicRight (initSeg x m) = dyadicRight (initSeg x N) := by
  refine Nat.le_induction rfl ?_
  intro m hm ih
  rw [initSeg_succ, hb m hm, dyadicRight_append_true, ih]

private theorem exists_rat_dyadicLeft (σ : BitString) : ∃ r : ℚ, dyadicLeft σ = (r : ℝ) := by
  refine ⟨(gridIndex σ : ℚ) / 2 ^ σ.length, ?_⟩
  rw [dyadicLeft_eq_gridPoint, gridPoint]
  push_cast
  ring

private theorem exists_rat_dyadicRight (σ : BitString) : ∃ r : ℚ, dyadicRight σ = (r : ℝ) := by
  refine ⟨((gridIndex σ : ℚ) + 1) / 2 ^ σ.length, ?_⟩
  rw [dyadicRight_eq_gridPoint_succ, gridPoint]
  push_cast
  ring

/-- **Bits change infinitely often.** -/
theorem frequently_bit_change_of_ne_rat {x : Cantor} (h : ∀ r : ℚ, realOf x ≠ (r : ℝ)) (N : ℕ) :
    ∃ n, N ≤ n ∧ x n ≠ x (n + 1) := by
  by_contra hcon
  have hstep : ∀ n, N ≤ n → x n = x (n + 1) := by
    intro n hn
    by_contra hne
    exact hcon ⟨n, hn, hne⟩
  have hconst := eq_of_no_bit_change hstep
  cases hxN : x N with
  | false =>
    have hb : ∀ n, N ≤ n → x n = false := fun n hn ↦ by rw [hconst n hn, hxN]
    have hmem : ∀ m, dyadicLeft (initSeg x N) ∈ dyadicInterval (initSeg x m) := by
      intro m
      rcases le_total N m with hm | hm
      · rw [dyadicInterval, Set.mem_Icc, ← dyadicLeft_initSeg_eq_of_false hb m hm]
        exact ⟨le_refl _, (dyadicLeft_lt_dyadicRight _).le⟩
      · refine dyadicInterval_subset_of_prefix (initSeg_prefix_of_le hm) ?_
        rw [dyadicInterval, Set.mem_Icc]
        exact ⟨le_refl _, (dyadicLeft_lt_dyadicRight _).le⟩
    obtain ⟨r, hr⟩ := exists_rat_dyadicLeft (initSeg x N)
    exact h r (by rw [← eq_realOf_of_mem_all_dyadicInterval hmem, hr])
  | true =>
    have hb : ∀ n, N ≤ n → x n = true := fun n hn ↦ by rw [hconst n hn, hxN]
    have hmem : ∀ m, dyadicRight (initSeg x N) ∈ dyadicInterval (initSeg x m) := by
      intro m
      rcases le_total N m with hm | hm
      · rw [dyadicInterval, Set.mem_Icc, ← dyadicRight_initSeg_eq_of_true hb m hm]
        exact ⟨(dyadicLeft_lt_dyadicRight _).le, le_refl _⟩
      · refine dyadicInterval_subset_of_prefix (initSeg_prefix_of_le hm) ?_
        rw [dyadicInterval, Set.mem_Icc]
        exact ⟨(dyadicLeft_lt_dyadicRight _).le, le_refl _⟩
    obtain ⟨r, hr⟩ := exists_rat_dyadicRight (initSeg x N)
    exact h r (by rw [← eq_realOf_of_mem_all_dyadicInterval hmem, hr])

/-- **The middle half.** At a bit change the point is a quarter-width away from both ends of its
cell. -/
theorem realOf_mem_middle_half_of_bit_change {x : Cantor} {n : ℕ} (h : x n ≠ x (n + 1)) :
    dyadicLeft (initSeg x n) + dyadicWidth (initSeg x n) / 4 ≤ realOf x ∧
      realOf x ≤ dyadicRight (initSeg x n) - dyadicWidth (initSeg x n) / 4 := by
  have hmem := realOf_mem_dyadicInterval x (n + 2)
  rw [dyadicInterval, Set.mem_Icc] at hmem
  have hstep : initSeg x (n + 2) = (initSeg x n ++ [x n]) ++ [x (n + 1)] := by
    rw [initSeg_succ, initSeg_succ]
  have hwpos := dyadicWidth_pos (initSeg x n)
  rw [hstep, dyadicRight] at hmem
  simp only [dyadicLeft_append, dyadicWidth_append] at hmem
  rw [dyadicRight]
  cases hb : x n <;> cases hb' : x (n + 1) <;> rw [hb, hb'] at hmem <;>
    simp only [Bool.false_eq_true, if_false, if_true] at hmem
  · exact absurd (by rw [hb, hb']) h
  · constructor <;> linarith [hmem.1, hmem.2]
  · constructor <;> linarith [hmem.1, hmem.2]
  · exact absurd (by rw [hb, hb']) h

end AlgorithmicRandomness
