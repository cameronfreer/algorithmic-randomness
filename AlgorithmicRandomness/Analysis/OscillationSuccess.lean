/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.OscillationFunction
import AlgorithmicRandomness.Analysis.InfiniteUpperDerivative

/-!
# Unbounded chord slopes of the oscillating function

Along the path of an irrational point `z`, the two recurrence properties of the parameters — high
betting cells and low waiting cells of arbitrarily small width around `z` — force the state to
switch infinitely often: an eventually constant state makes the path a binary tail in one grid,
which visits a witness cell exactly, and the retained state's own certificate contradicts the
witness slope there.

Every complete waiting→betting→waiting→betting cycle multiplies the chord slope of the assigned
values at the switching parents by `δ = (γ − margin)/(β + margin) > 1`, through the two mass
identities of the invariant and the two switch certificates. Since the switching parents occur
arbitrarily late and their widths tend to zero, the bundled function has unbounded chord slopes
straddling `z`, so its upper derivative at `z` is infinite. No point or witness enters before the
recurrence hypotheses; those are stated as a structure so that no private witness is needed here.
-/

open Filter Topology

open scoped NNRat

namespace AlgorithmicRandomness

attribute [local irreducible] ComputableMonotone.addIdentity OscInterpStep.weightCode
  OscInterpStep.mixCode OscInterpStep.applyCode OscNode.slopeCode

variable (f : ComputableMonotone) (P : OscillationParams)

/-! ## The bridge -/

theorem oscMonotone_toFun_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (oscMonotone f P).toFun x = oscFun f P x := by
  rw [(oscMonotone f P).toFun_of_mem hx]
  exact oscMonotone_unitFun f P ⟨x, hx⟩

namespace OscNode

/-- The chord slope of the assigned values across a node. -/
noncomputable def gSlope (n : OscNode) : ℝ := n.toOscFrame.mass f / n.interval.width

/-- The chord slope of the strictified source across a node. -/
noncomputable def srcSlope (n : OscNode) : ℝ :=
  slope f.addIdentity.toFun n.interval.left n.interval.right

theorem interval_right_sub_left (n : OscNode) :
    n.interval.right - n.interval.left = n.interval.width := by
  rw [RatIntervalCode.right]; ring

/-- The chord slope of the bundled function across a reachable node is the chord slope of the
assigned values. -/
theorem slope_oscMonotone {p : List OscMove} {n : OscNode} (hn : rawNode f P p = some n) :
    slope (oscMonotone f P).toFun n.interval.left n.interval.right = gSlope f n := by
  have h := Inv.of_rawNode f P hn
  have hc := h.connected
  have hl := oscFun.endpoint f P ⟨p, false, n, hn⟩
  have hr := oscFun.endpoint f P ⟨p, true, n, hn⟩
  simp only [Endpoint.coord, Endpoint.value, coord, value, cond_true, cond_false] at hl hr
  have hw := hc.width_pos
  have hrl := interval_right_sub_left n
  have hl1 : n.interval.left ≤ 1 := by linarith [hc.right_le_one]
  have hr0 : 0 ≤ n.interval.right := by linarith [hc.left_nonneg]
  rw [slope_def_field, gSlope, OscFrame.mass, interval_right_sub_left,
    oscMonotone_toFun_of_mem f P ⟨hc.left_nonneg, hl1⟩,
    oscMonotone_toFun_of_mem f P ⟨hr0, hc.right_le_one⟩, hl, hr]

theorem gSlope_pos {n : OscNode} (h : Inv f P n) : 0 < gSlope f n :=
  div_pos (h.mass_pos f P) h.connected.width_pos

/-! ## The certificates at switches -/

theorem srcSlode_pos {n : OscNode} (h : Inv f P n) : 0 < srcSlope f n := by
  have hc := h.connected
  have hw := hc.width_pos
  rw [srcSlope, slope_def_field, interval_right_sub_left]
  refine div_pos ?_ hw
  linarith [width_le_addIdentity_gap f hc.left_nonneg hc.right_le_one]

/-- The chord slope of the source across a node, times the width, is the source increment. -/
theorem srcSlope_mul_width {n : OscNode} (hw : 0 < n.interval.width) :
    srcSlope f n * n.interval.width
      = f.addIdentity.toFun n.interval.right - f.addIdentity.toFun n.interval.left := by
  rw [srcSlope, slope_def_field, interval_right_sub_left, div_mul_cancel₀ _ hw.ne']

/-- The sample against the source slope, on a nondegenerate node. -/
private theorem abs_sample_sub_srcSlope {n : OscNode} (hw : 0 < n.interval.width) :
    |((RatCode.value (slopeCode f P n) : ℚ) : ℝ) - srcSlope f n| ≤ P.margin :=
  slopeCode_error f P n hw

/-- Switching from waiting into betting certifies a low source slope on the parent. -/
theorem srcSlope_lt_of_switch_to_betting {n : OscNode} (hw : 0 < n.interval.width)
    (hb : n.betting = false) (hn : nextBetting f P n = true) :
    srcSlope f n < P.beta + P.margin := by
  have herr := (abs_le.mp (abs_sample_sub_srcSlope f P hw)).1
  rw [nextBetting, hb, cond_false, RatCode.lt_iff, RatCode.value_ofNNRat] at hn
  have h : ((RatCode.value (slopeCode f P n) : ℚ) : ℝ) < P.beta := by
    rw [OscillationParams.beta]; exact_mod_cast hn
  linarith

/-- Switching from betting into waiting certifies a high source slope on the parent. -/
theorem srcSlope_gt_of_switch_to_waiting {n : OscNode} (hw : 0 < n.interval.width)
    (hb : n.betting = true) (hn : nextBetting f P n = false) :
    P.gamma - P.margin < srcSlope f n := by
  have herr := (abs_le.mp (abs_sample_sub_srcSlope f P hw)).2
  rw [nextBetting, hb, cond_true, Bool.not_eq_false', RatCode.lt_iff, RatCode.value_ofNNRat] at hn
  have h : P.gamma < ((RatCode.value (slopeCode f P n) : ℚ) : ℝ) := by
    rw [OscillationParams.gamma]; exact_mod_cast hn
  linarith

/-- Staying in waiting certifies that the source slope is not low. -/
theorem srcSlope_ge_of_stay_waiting {n : OscNode} (hw : 0 < n.interval.width)
    (hb : n.betting = false) (hn : nextBetting f P n = false) :
    P.beta - P.margin ≤ srcSlope f n := by
  have herr := (abs_le.mp (abs_sample_sub_srcSlope f P hw)).2
  rw [nextBetting, hb, cond_false, Bool.eq_false_iff] at hn
  have hlt : ¬ RatCode.value (slopeCode f P n) < RatCode.value (RatCode.ofNNRat P.betaCode) :=
    fun h ↦ hn ((RatCode.lt_iff _ _).mpr h)
  rw [RatCode.value_ofNNRat, not_lt] at hlt
  have h : P.beta ≤ ((RatCode.value (slopeCode f P n) : ℚ) : ℝ) := by
    rw [OscillationParams.beta]; exact_mod_cast hlt
  linarith

/-- Staying in betting certifies that the source slope is not high (restated on `srcSlope`). -/
theorem srcSlope_le_of_stay_betting {n : OscNode} (hw : 0 < n.interval.width)
    (hn : nextBetting f P n = true) : srcSlope f n ≤ P.gamma + P.margin :=
  slope_le_of_nextBetting f P hw hn

/-! ## Binary tails -/

/-- An edge that keeps the state on a node with a cell is a binary subdivision. -/
theorem Step.binary_of_not_switched {n n' : OscNode} (hs : Step f P n n')
    (hb : n'.betting = n.betting) (hc : n.cell.isSome = true) : ∃ b, n' = binaryNode n b := by
  rcases hs.elim f P with ⟨b, -, rfl⟩ | ⟨c, hneed, -, rfl⟩
  · exact ⟨b, rfl⟩
  · exfalso
    have hnb : nextBetting f P n = n.betting := by
      rw [← hs.betting_eq_nextBetting f P]; exact hb
    rw [needsRegrid, Bool.or_eq_true, hc] at hneed
    rcases hneed with h | h
    · exact (switched_iff _ _).mp h hnb
    · simp at h

end OscNode

namespace OscPath

variable {f P} (γ : OscPath f P)

/-- Under an eventually constant state, every edge from `max k₀ 1` on is binary. -/
theorem binary_of_const {k₀ : ℕ}
    (hconst : ∀ k, k₀ ≤ k → (γ.node (k + 1)).betting = (γ.node k).betting)
    {k : ℕ} (hk : max k₀ 1 ≤ k) : ∃ b, γ.node (k + 1) = OscNode.binaryNode (γ.node k) b := by
  have hk₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk₁ : 1 ≤ k := le_trans (le_max_right _ _) hk
  refine (γ.step k).binary_of_not_switched f P (hconst k hk₀) ?_
  have := (γ.step (k - 1)).cell_isSome f P
  rwa [show k - 1 + 1 = k by omega] at this

/-- Along a binary tail the cell grows by one bit per edge, in the same block. -/
theorem cell_of_binary_tail {k₁ : ℕ} {c₀ : AffineDyadicCell}
    (hbin : ∀ k, k₁ ≤ k → ∃ b, γ.node (k + 1) = OscNode.binaryNode (γ.node k) b)
    (hc₀ : (γ.node k₁).cell = some c₀) (i : ℕ) :
    ∃ c : AffineDyadicCell, (γ.node (k₁ + i)).cell = some c ∧ c.block = c₀.block ∧
      c.word.length = c₀.word.length + i := by
  induction i with
  | zero => exact ⟨c₀, by simpa using hc₀, rfl, by simp⟩
  | succ i ih =>
    obtain ⟨c, hc, hb, hl⟩ := ih
    obtain ⟨b, hstep⟩ := hbin (k₁ + i) (by omega)
    refine ⟨c.child b, ?_, hb, ?_⟩
    · rw [show k₁ + (i + 1) = k₁ + i + 1 by ring, hstep]
      simp only [OscNode.binaryNode, hc, Option.map_some]
    · rw [AffineDyadicCell.child_word, List.length_append, List.length_singleton, hl]
      ring

/-- **Exact visit.** A binary tail in grid `G` through the irrational `z` visits exactly every
`G`-cell `⟨0, σ⟩` containing `z` whose word is at least as long as the tail's first word. -/
theorem exists_visit {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) {k₁ : ℕ} {c₀ : AffineDyadicCell}
    (hbin : ∀ k, k₁ ≤ k → ∃ b, γ.node (k + 1) = OscNode.binaryNode (γ.node k) b)
    (hc₀ : (γ.node k₁).cell = some c₀) {G : AffineDyadicGrid}
    (hgrid : ∀ k, k₁ ≤ k → OscNode.gridOf P (γ.node k).betting = G) {σ : BitString}
    (hσ : z ∈ G.interval σ) (hlen : c₀.word.length ≤ σ.length) :
    ∃ k, k₁ ≤ k ∧ (γ.node k).cell = some ⟨0, σ⟩ := by
  obtain ⟨c, hc, -, hl⟩ := γ.cell_of_binary_tail hbin hc₀ (σ.length - c₀.word.length)
  refine ⟨k₁ + (σ.length - c₀.word.length), by omega, ?_⟩
  rw [hc]
  have hinv := γ.inv (k₁ + (σ.length - c₀.word.length))
  have hI := hinv.cell_some c hc
  rw [hgrid _ (by omega)] at hI
  have hzc : z ∈ G.cellInterval c := by
    rw [← AffineDyadicGrid.interval_cellCode, ← hI]
    exact hz _
  have hzσ : z ∈ G.cellInterval ⟨0, σ⟩ := by
    rw [AffineDyadicGrid.cellInterval_mk_zero]
    exact hσ
  have hlen' : c.word.length = σ.length := by omega
  rcases comparable_of_mem_cellIntervals_of_ne_rat hirr hzc hzσ with ⟨hb, hw⟩ | ⟨hb, hw⟩
  · have := hw.eq_of_length hlen'
    cases c
    simp only at hb this
    rw [hb, this]
  · have := hw.eq_of_length hlen'.symm
    cases c
    simp only at hb this
    rw [← hb, ← this]

end OscPath

/-! ## Infinite switching -/

/-- The two recurrence properties of the parameters at `z`, stated on the strictified source's
chord slopes over grid cells. -/
structure Recurrent (z : ℝ) : Prop where
  /-- Betting cells of arbitrarily small width around `z` with slope above `γ + margin`. -/
  high : ∀ ε : ℝ, 0 < ε → ∃ σ : BitString, z ∈ P.betGrid.interval σ ∧ P.betGrid.width σ < ε ∧
    P.gamma + P.margin < slope f.addIdentity.toFun (P.betGrid.left σ) (P.betGrid.right σ)
  /-- Waiting cells of arbitrarily small width around `z` with slope below `β − margin`. -/
  low : ∀ ε : ℝ, 0 < ε → ∃ σ : BitString, z ∈ P.waitGrid.interval σ ∧ P.waitGrid.width σ < ε ∧
    slope f.addIdentity.toFun (P.waitGrid.left σ) (P.waitGrid.right σ) < P.beta - P.margin

namespace OscPath

variable {f P} (γ : OscPath f P)

/-- The source slope over a node whose cell is `⟨0, σ⟩` in grid `G` is the slope over the grid
cell `σ`. -/
theorem srcSlope_of_cell_zero {k : ℕ} {σ : BitString} (hc : (γ.node k).cell = some ⟨0, σ⟩) :
    OscNode.srcSlope f (γ.node k)
      = slope f.addIdentity.toFun ((OscNode.gridOf P (γ.node k).betting).left σ)
        ((OscNode.gridOf P (γ.node k).betting).right σ) := by
  have hI := (γ.inv k).cell_some _ hc
  rw [OscNode.srcSlope, hI, AffineDyadicGrid.left_cellCode, AffineDyadicGrid.right_cellCode,
    AffineDyadicGrid.cellLeft_mk_zero, AffineDyadicGrid.cellRight_mk_zero]

/-- A grid cell narrower than a node's cell has a longer word. -/
theorem word_length_lt_of_width_lt {G : AffineDyadicGrid} {c : AffineDyadicCell} {σ : BitString}
    (h : G.width σ < G.cellWidth c) : c.word.length < σ.length := by
  rw [AffineDyadicGrid.width, AffineDyadicGrid.cellWidth, dyadicWidth, dyadicWidth] at h
  have hs := G.zero_lt_scale
  have h' : (2⁻¹ : ℝ) ^ σ.length < (2⁻¹ : ℝ) ^ c.word.length := lt_of_mul_lt_mul_left h hs.le
  exact (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mp h'

/-- **Infinite switching.** With the recurrence properties at an irrational `z` on the path, the
state switches after every index. -/
theorem exists_switch_after {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) (k₀ : ℕ) :
    ∃ k, k₀ ≤ k ∧ (γ.node (k + 1)).betting ≠ (γ.node k).betting := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ k, k₀ ≤ k → (γ.node (k + 1)).betting = (γ.node k).betting := hcon
  set k₁ := max k₀ 1 with hk₁
  have hbin : ∀ k, k₁ ≤ k → ∃ b, γ.node (k + 1) = OscNode.binaryNode (γ.node k) b :=
    fun k hk ↦ γ.binary_of_const hconst hk
  have hstate : ∀ k, k₁ ≤ k → (γ.node k).betting = (γ.node k₁).betting := by
    intro k hk
    induction k with
    | zero => rw [Nat.le_zero.mp hk]
    | succ k ih =>
      rcases Nat.lt_or_ge k k₁ with hlt | hge
      · have : k + 1 = k₁ := by omega
        rw [this]
      · rw [hconst k (by omega), ih hge]
  have hgrid : ∀ k, k₁ ≤ k →
      OscNode.gridOf P (γ.node k).betting = OscNode.gridOf P (γ.node k₁).betting :=
    fun k hk ↦ by rw [hstate k hk]
  have hsome := (γ.step (k₁ - 1)).cell_isSome f P
  rw [show k₁ - 1 + 1 = k₁ by omega] at hsome
  obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp hsome
  have hI₀ := (γ.inv k₁).cell_some c₀ hc₀
  have hw₀ : 0 < (γ.node k₁).interval.width := γ.width_pos k₁
  -- the constant state selects the grid and the witness family
  cases hs : (γ.node k₁).betting
  · -- eventually waiting: a low cell is visited while waiting is retained
    obtain ⟨σ, hzσ, hwσ, hslope⟩ := hR.low _ hw₀
    have hG : OscNode.gridOf P (γ.node k₁).betting = P.waitGrid := by rw [hs]; rfl
    have hlen : c₀.word.length ≤ σ.length := by
      refine (word_length_lt_of_width_lt (G := P.waitGrid) ?_).le
      rw [hI₀, hG, AffineDyadicGrid.width_cellCode] at hw₀ hwσ
      exact hwσ
    obtain ⟨k, hk, hck⟩ := γ.exists_visit hz hirr hbin hc₀ (G := P.waitGrid)
      (fun k hk ↦ by rw [hgrid k hk, hG]) hzσ hlen
    have hbk : (γ.node k).betting = false := by rw [hstate k hk, hs]
    have hnb : OscNode.nextBetting f P (γ.node k) = false := by
      rw [← (γ.step k).betting_eq_nextBetting f P, hconst k (by omega), hbk]
    have hge := OscNode.srcSlope_ge_of_stay_waiting f P (γ.width_pos k) hbk hnb
    rw [γ.srcSlope_of_cell_zero hck, hbk] at hge
    exact absurd (lt_of_le_of_lt hge hslope) (lt_irrefl _)
  · -- eventually betting: a high cell is visited while betting is retained
    obtain ⟨σ, hzσ, hwσ, hslope⟩ := hR.high _ hw₀
    have hG : OscNode.gridOf P (γ.node k₁).betting = P.betGrid := by rw [hs]; rfl
    have hlen : c₀.word.length ≤ σ.length := by
      refine (word_length_lt_of_width_lt (G := P.betGrid) ?_).le
      rw [hI₀, hG, AffineDyadicGrid.width_cellCode] at hw₀ hwσ
      exact hwσ
    obtain ⟨k, hk, hck⟩ := γ.exists_visit hz hirr hbin hc₀ (G := P.betGrid)
      (fun k hk ↦ by rw [hgrid k hk, hG]) hzσ hlen
    have hbk : (γ.node k).betting = true := by rw [hstate k hk, hs]
    have hnb : OscNode.nextBetting f P (γ.node k) = true := by
      rw [← (γ.step k).betting_eq_nextBetting f P, hconst k (by omega), hbk]
    have hle := OscNode.srcSlope_le_of_stay_betting f P (γ.width_pos k) hnb
    rw [γ.srcSlope_of_cell_zero hck, hbk] at hle
    exact absurd (lt_of_lt_of_le hslope hle) (lt_irrefl _)

end OscPath

/-! ## Switching parents and geometric growth -/

namespace OscPath

variable {f P} (γ : OscPath f P)

/-- A waiting→betting switching parent. -/
def WB (k : ℕ) : Prop := (γ.node k).betting = false ∧ (γ.node (k + 1)).betting = true

/-- A betting→waiting switching parent. -/
def BW (k : ℕ) : Prop := (γ.node k).betting = true ∧ (γ.node (k + 1)).betting = false

/-- The first switch at or after `N`, with the state constant before it. -/
theorem exists_first_switch {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) (N : ℕ) :
    ∃ k, N ≤ k ∧ (γ.node (k + 1)).betting ≠ (γ.node k).betting ∧
      ∀ i, N ≤ i → i < k → (γ.node (i + 1)).betting = (γ.node i).betting := by
  classical
  have hex : ∃ m, (γ.node (N + m + 1)).betting ≠ (γ.node (N + m)).betting := by
    obtain ⟨k, hk, hsw⟩ := γ.exists_switch_after hz hirr hR N
    exact ⟨k - N, by rw [show N + (k - N) = k by omega]; exact hsw⟩
  refine ⟨N + Nat.find hex, by omega, Nat.find_spec hex, fun i hi hik ↦ ?_⟩
  have := Nat.find_min hex (m := i - N) (by omega)
  rw [show N + (i - N) = i by omega] at this
  exact not_ne_iff.mp this

/-- The state is constant across a stretch without switches. -/
theorem betting_const {N k : ℕ}
    (hno : ∀ i, N ≤ i → i < k → (γ.node (i + 1)).betting = (γ.node i).betting) :
    ∀ i, N ≤ i → i ≤ k → (γ.node i).betting = (γ.node N).betting := by
  intro i hNi hik
  induction i with
  | zero => rw [Nat.le_zero.mp hNi]
  | succ i ih =>
    rcases Nat.lt_or_ge i N with hlt | hge
    · have : i + 1 = N := by omega
      rw [this]
    · rw [hno i hge (by omega), ih hge (by omega)]

/-- The anchor along a constant stretch after a switch is the frame of the switching parent. -/
theorem phaseStart_eq_of_stretch {a b : ℕ} (hab : a < b)
    (hsw : (γ.node (a + 1)).betting ≠ (γ.node a).betting)
    (hmid : ∀ i, a < i → i ≤ b → (γ.node i).betting = (γ.node (a + 1)).betting) :
    (γ.node b).phaseStart = (γ.node a).toOscFrame := by
  have key : ∀ i, a < i → i ≤ b → (γ.node i).phaseStart = (γ.node a).toOscFrame := by
    intro i hai hib
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.lt_or_ge i (a + 1) with hlt | hge
      · have : i = a := by omega
        subst this
        exact (γ.step i).anchor_eq_of_switched f P hsw
      · rw [(γ.step i).anchor_eq_of_not_switched f P
          (by rw [hmid (i + 1) (by omega) hib, hmid i (by omega) (by omega)])]
        exact ih (by omega) (by omega)
  exact key b hab le_rfl

/-- **One cycle.** `A` a waiting→betting parent, `B` the next betting→waiting parent, `C` the next
waiting→betting parent: the chord slope of the values grows by the factor `δ`. -/
theorem gSlope_cycle {a b c : ℕ} (hab : a < b) (hbc : b < c) (hA : γ.WB a) (hB : γ.BW b)
    (hC : γ.WB c) (hmidAB : ∀ i, a < i → i ≤ b → (γ.node i).betting = true)
    (hmidBC : ∀ i, b < i → i ≤ c → (γ.node i).betting = false) :
    (P.gamma - P.margin) / (P.beta + P.margin) * OscNode.gSlope f (γ.node a)
      ≤ OscNode.gSlope f (γ.node c) := by
  have hinvA := γ.inv a
  have hinvB := γ.inv b
  have hinvC := γ.inv c
  have hwA := γ.width_pos a
  have hwB := γ.width_pos b
  have hwC := γ.width_pos c
  -- anchors
  have hanchorB : (γ.node b).phaseStart = (γ.node a).toOscFrame :=
    γ.phaseStart_eq_of_stretch hab (by rw [hA.1, hA.2]; decide)
      (fun i hai hib ↦ by rw [hmidAB i hai hib, hA.2])
  have hanchorC : (γ.node c).phaseStart = (γ.node b).toOscFrame :=
    γ.phaseStart_eq_of_stretch hbc (by rw [hB.1, hB.2]; decide)
      (fun i hbi hic ↦ by rw [hmidBC i hbi hic, hB.2])
  -- the two mass identities
  have hmb := hinvB.mass_betting f P hB.1
  rw [hanchorB] at hmb
  have hmw := hinvC.mass_waiting f P hC.1
  rw [hanchorC] at hmw
  -- the two switch certificates
  have hsA := OscNode.srcSlope_lt_of_switch_to_betting f P hwA hA.1
    (by rw [← (γ.step a).betting_eq_nextBetting f P]; exact hA.2)
  have hsB := OscNode.srcSlope_gt_of_switch_to_waiting f P hwB hB.1
    (by rw [← (γ.step b).betting_eq_nextBetting f P]; exact hB.2)
  have hsA0 := OscNode.srcSlode_pos f P hinvA
  have hsB0 := OscNode.srcSlode_pos f P hinvB
  have hβ : 0 ≤ P.beta := by rw [OscillationParams.beta]; positivity
  have hm := P.margin_pos
  have hγm : 0 < P.gamma - P.margin := by linarith [P.beta_add_margin_lt]
  -- the growth from `A` to `B`
  have hFA := OscNode.srcSlope_mul_width f hwA
  have hFB := OscNode.srcSlope_mul_width f hwB
  have key : (γ.node b).toOscFrame.mass f * OscNode.srcSlope f (γ.node a)
        * (γ.node a).interval.width
      = (γ.node a).toOscFrame.mass f * OscNode.srcSlope f (γ.node b)
        * (γ.node b).interval.width := by
    calc (γ.node b).toOscFrame.mass f * OscNode.srcSlope f (γ.node a) * (γ.node a).interval.width
        = (γ.node b).toOscFrame.mass f
          * (OscNode.srcSlope f (γ.node a) * (γ.node a).interval.width) := by ring
      _ = (γ.node a).toOscFrame.mass f
          * (OscNode.srcSlope f (γ.node b) * (γ.node b).interval.width) := by
          rw [hFA, hFB]; exact hmb
      _ = _ := by ring
  have hgB : OscNode.gSlope f (γ.node b) * OscNode.srcSlope f (γ.node a)
      = OscNode.gSlope f (γ.node a) * OscNode.srcSlope f (γ.node b) := by
    rw [OscNode.gSlope, OscNode.gSlope, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_div_iff hwB.ne' hwA.ne']
    linear_combination key
  have hgB' : OscNode.gSlope f (γ.node b)
      = OscNode.gSlope f (γ.node a)
        * (OscNode.srcSlope f (γ.node b) / OscNode.srcSlope f (γ.node a)) := by
    rw [← mul_div_assoc]
    exact eq_div_of_mul_eq hsA0.ne' hgB
  -- the transfer from `B` to `C`
  have hgC : OscNode.gSlope f (γ.node c) = OscNode.gSlope f (γ.node b) := by
    rw [OscNode.gSlope, OscNode.gSlope, div_eq_div_iff hwC.ne' hwB.ne']
    linear_combination hmw
  rw [hgC, hgB', mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (OscNode.gSlope_pos f P hinvA).le
  exact div_le_div₀ hsB0.le hsB.le hsA0 hsA.le

/-- After a waiting→betting parent there is a later one with chord slope grown by `δ`. -/
theorem exists_next_parent {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) {a : ℕ} (hA : γ.WB a) :
    ∃ c, a < c ∧ γ.WB c ∧
      (P.gamma - P.margin) / (P.beta + P.margin) * OscNode.gSlope f (γ.node a)
        ≤ OscNode.gSlope f (γ.node c) := by
  obtain ⟨b, hab, hswb, hnob⟩ := γ.exists_first_switch hz hirr hR (a + 1)
  have hconstb := γ.betting_const hnob
  have hbb : (γ.node b).betting = true := by rw [hconstb b hab le_rfl, hA.2]
  have hB : γ.BW b := ⟨hbb, by
    cases h : (γ.node (b + 1)).betting
    · rfl
    · exact absurd (h.trans hbb.symm) hswb⟩
  obtain ⟨c, hbc, hswc, hnoc⟩ := γ.exists_first_switch hz hirr hR (b + 1)
  have hconstc := γ.betting_const hnoc
  have hcb : (γ.node c).betting = false := by rw [hconstc c hbc le_rfl, hB.2]
  have hC : γ.WB c := ⟨hcb, by
    cases h : (γ.node (c + 1)).betting
    · exact absurd (h.trans hcb.symm) hswc
    · rfl⟩
  refine ⟨c, by omega, hC, γ.gSlope_cycle (by omega) (by omega) hA hB hC ?_ ?_⟩
  · intro i hai hib
    rw [hconstb i (by omega) hib, hA.2]
  · intro i hbi hic
    rw [hconstc i (by omega) hic, hB.2]

/-- Some waiting→betting parent exists. -/
theorem exists_WB {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) : ∃ a, γ.WB a := by
  obtain ⟨k, -, hsw, hno⟩ := γ.exists_first_switch hz hirr hR 0
  cases hk : (γ.node k).betting
  · exact ⟨k, hk, by
      cases h : (γ.node (k + 1)).betting
      · exact absurd (h.trans hk.symm) hsw
      · rfl⟩
  · -- the first switch is betting→waiting; the next one is waiting→betting
    have hk1 : (γ.node (k + 1)).betting = false := by
      cases h : (γ.node (k + 1)).betting
      · rfl
      · exact absurd (h.trans hk.symm) hsw
    obtain ⟨c, hkc, hswc, hnoc⟩ := γ.exists_first_switch hz hirr hR (k + 1)
    have hcb : (γ.node c).betting = false := by rw [γ.betting_const hnoc c hkc le_rfl, hk1]
    exact ⟨c, hcb, by
      cases h : (γ.node (c + 1)).betting
      · exact absurd (h.trans hcb.symm) hswc
      · rfl⟩

/-- The sequence of switching parents, each with chord slope grown by `δ` over the previous. -/
noncomputable def parents {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) : ℕ → {a : ℕ // γ.WB a}
  | 0 => ⟨Classical.choose (γ.exists_WB hz hirr hR), Classical.choose_spec (γ.exists_WB hz hirr hR)⟩
  | j + 1 =>
    let p := parents hz hirr hR j
    ⟨Classical.choose (γ.exists_next_parent hz hirr hR p.2),
      (Classical.choose_spec (γ.exists_next_parent hz hirr hR p.2)).2.1⟩

theorem parents_lt {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) (j : ℕ) :
    (γ.parents hz hirr hR j).1 < (γ.parents hz hirr hR (j + 1)).1 :=
  (Classical.choose_spec (γ.exists_next_parent hz hirr hR (γ.parents hz hirr hR j).2)).1

theorem parents_growth {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) (j : ℕ) :
    (P.gamma - P.margin) / (P.beta + P.margin)
        * OscNode.gSlope f (γ.node (γ.parents hz hirr hR j).1)
      ≤ OscNode.gSlope f (γ.node (γ.parents hz hirr hR (j + 1)).1) :=
  (Classical.choose_spec (γ.exists_next_parent hz hirr hR (γ.parents hz hirr hR j).2)).2.2

theorem le_parents {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) (j : ℕ) :
    j ≤ (γ.parents hz hirr hR j).1 := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => exact lt_of_le_of_lt ih (γ.parents_lt hz hirr hR j)

/-- **Cofinal geometric growth.** Waiting→betting parents with chord slope at least `c₀ δ^j` occur
after every index. -/
theorem exists_gSlope_ge {z : ℝ} (hz : ∀ k, z ∈ (γ.node k).interval.interval)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ j N : ℕ, ∃ k, N ≤ k ∧ γ.WB k ∧
      c₀ * ((P.gamma - P.margin) / (P.beta + P.margin)) ^ j ≤ OscNode.gSlope f (γ.node k) := by
  set δ := (P.gamma - P.margin) / (P.beta + P.margin) with hδ
  have hβ : 0 ≤ P.beta := by rw [OscillationParams.beta]; positivity
  have hδ1 : 1 < δ := P.one_lt_ratio hβ
  refine ⟨OscNode.gSlope f (γ.node (γ.parents hz hirr hR 0).1),
    OscNode.gSlope_pos f P (γ.inv _), fun j N ↦ ?_⟩
  have hgrow : ∀ j, OscNode.gSlope f (γ.node (γ.parents hz hirr hR 0).1) * δ ^ j
      ≤ OscNode.gSlope f (γ.node (γ.parents hz hirr hR j).1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc OscNode.gSlope f (γ.node (γ.parents hz hirr hR 0).1) * δ ^ (j + 1)
          = δ * (OscNode.gSlope f (γ.node (γ.parents hz hirr hR 0).1) * δ ^ j) := by ring
        _ ≤ δ * OscNode.gSlope f (γ.node (γ.parents hz hirr hR j).1) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ _ := γ.parents_growth hz hirr hR j
  refine ⟨(γ.parents hz hirr hR (max j N)).1,
    le_trans (le_max_right _ _) (γ.le_parents hz hirr hR _), (γ.parents hz hirr hR _).2, ?_⟩
  refine le_trans ?_ (hgrow (max j N))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hδ1.le (le_max_left _ _))
    (OscNode.gSlope_pos f P (γ.inv _)).le

end OscPath

/-! ## The infinite upper derivative -/

/-- A local slope bound based at `z` bounds the chords straddling `z`. -/
theorem slope_le_of_straddle {g : ℝ → ℝ} {z C ε : ℝ}
    (h : ∀ y, y ≠ z → |y - z| < ε → slope g z y ≤ C) {a b : ℝ} (ha : a < z) (hb : z < b)
    (hε : b - a < ε) : slope g a b ≤ C := by
  have hb' := h b hb.ne' (by rw [abs_lt]; constructor <;> linarith)
  have ha' := h a ha.ne (by rw [abs_lt]; constructor <;> linarith)
  rw [slope_def_field, div_le_iff₀ (by linarith)] at hb'
  rw [slope_def_field, div_le_iff_of_neg (by linarith)] at ha'
  rw [slope_def_field, div_le_iff₀ (by linarith)]
  linarith

/-- **Unbounded chord slopes.** With the recurrence properties at an irrational `z` of the unit
interval, the bundled function has no finite upper derivative at `z`. -/
theorem not_finiteUpperDerivativeAt_oscMonotone {z : ℝ} (hz01 : z ∈ Set.Icc (0 : ℝ) 1)
    (hirr : ∀ q : ℚ, z ≠ (q : ℝ)) (hR : Recurrent f P z) :
    ¬ FiniteUpperDerivativeAt (oscMonotone f P).toFun z := by
  intro hfin
  rw [finiteUpperDerivativeAt_iff] at hfin
  obtain ⟨C, ε, hε, hC⟩ := hfin
  obtain ⟨γ, hz⟩ := OscNode.exists_oscPath_mem f P hirr hz01
  obtain ⟨c₀, hc₀, hgrow⟩ := γ.exists_gSlope_ge hz hirr hR
  set δ := (P.gamma - P.margin) / (P.beta + P.margin) with hδ
  have hβ : 0 ≤ P.beta := by rw [OscillationParams.beta]; positivity
  have hδ1 : 1 < δ := P.one_lt_ratio hβ
  obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hδ1).eventually
    (eventually_gt_atTop (C / c₀))).exists
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.1 γ.width_tendsto_zero).2 ε hε)
  obtain ⟨k, hk, -, hg⟩ := hgrow j N
  obtain ⟨p, hp⟩ := γ.exists_path k
  have hslope := OscNode.slope_oscMonotone f P hp
  have hzk := hz k
  rw [RatIntervalCode.interval, Set.mem_Icc] at hzk
  have hlt : (γ.node k).interval.left < z :=
    lt_of_le_of_ne hzk.1 fun h ↦ hirr (RatCode.value (γ.node k).interval.leftCode) h.symm
  have hgt : z < (γ.node k).interval.right :=
    lt_of_le_of_ne hzk.2 fun h ↦ hirr (RatCode.value (γ.node k).interval.rightCode)
      (by rw [h]; exact (RatIntervalCode.value_rightCode _).symm)
  have hstrad := slope_le_of_straddle hC hlt hgt
    (by rw [OscNode.interval_right_sub_left]; exact hN k hk)
  rw [hslope] at hstrad
  have hCj : C < c₀ * δ ^ j := by
    rw [div_lt_iff₀ hc₀] at hj
    linarith
  linarith

end AlgorithmicRandomness
