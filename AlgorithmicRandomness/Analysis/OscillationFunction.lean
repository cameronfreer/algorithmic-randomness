/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.OscillationInvariant
import Mathlib.NumberTheory.Real.Irrational

/-!
# The oscillating function

The endpoint values assigned along the tree of `OscillationTree` are collected into one function
on the unit interval, which is then packaged as a `ComputableMonotone`.

An endpoint *name* is a successful finite path together with a side. The first task is the global
ordering of values by coordinates, across branches: it is what makes the supremum over endpoints
at or below a point well behaved, and what makes a bracket of two names a sound certificate for
the approximation program. Agreement between two names of one coordinate is antisymmetry.

Continuity is the substantive part. Along an infinite path the mass tends to zero, but a rational
point need not lie on any infinite path: the regridding children of a node cover its irrational
points only. At such a *stopped* point the function agrees with the parent's continuous
interpolation, which is what controls the omitted point from both sides. No uniform depth bound
and no local finiteness enter.
-/

open Filter Topology

open scoped NNRat

namespace AlgorithmicRandomness

-- The coded programs are used only through their contracts; see `OscillationTree`.
attribute [local irreducible] ComputableMonotone.addIdentity OscInterpStep.weightCode
  OscInterpStep.mixCode OscInterpStep.applyCode OscNode.slopeCode OscNode.nextBetting

/-- A move of the construction. -/
abbrev OscMove := Bool ⊕ AffineDyadicCell

namespace OscNode

variable (f : ComputableMonotone) (P : OscillationParams)

/-! ## The recursion restarted at a node -/

/-- The node reached from `n` along `path`, if every move is allowed. -/
noncomputable def rawNodeFrom (n : OscNode) (path : List OscMove) : Option OscNode :=
  path.foldl (fun o m ↦ o.bind fun n ↦ step f P n m) (some n)

theorem rawNode_eq_rawNodeFrom (path : List OscMove) :
    rawNode f P path = rawNodeFrom f P root path := rfl

@[simp] theorem rawNodeFrom_nil (n : OscNode) : rawNodeFrom f P n [] = some n := rfl

private theorem foldl_none (path : List OscMove) :
    path.foldl (fun o m ↦ o.bind fun n ↦ step f P n m) none = none := by
  induction path with
  | nil => rfl
  | cons m p ih => rw [List.foldl_cons, Option.bind_none, ih]

theorem rawNodeFrom_cons (n : OscNode) (m : OscMove) (path : List OscMove) :
    rawNodeFrom f P n (m :: path) = (step f P n m).bind fun n' ↦ rawNodeFrom f P n' path := by
  rw [rawNodeFrom, List.foldl_cons, Option.bind_some]
  cases step f P n m with
  | none => rw [Option.bind_none, foldl_none]
  | some n' => rfl

/-- The interpolation that computes the values of every child of `n`. -/
noncomputable def childInterp (n : OscNode) (t : ℝ) : ℝ :=
  interp f (nextBetting f P n) n.interval (n.toOscFrame.eval f).1 (n.toOscFrame.eval f).2 t

theorem Step.eval_eq_childInterp {n c : OscNode} (h : Inv f P n) (hs : Step f P n c) :
    (c.toOscFrame.eval f).1 = childInterp f P n c.interval.left ∧
      (c.toOscFrame.eval f).2 = childInterp f P n c.interval.right := by
  rw [hs.eval_eq f P h, hs.betting_eq_nextBetting f P]
  exact ⟨rfl, rfl⟩

theorem childInterp_mono {n : OscNode} (h : Inv f P n) {s t : ℝ} (hst : s ≤ t) :
    childInterp f P n s ≤ childInterp f P n t := by
  have hc := h.connected
  have hθ := interpWeight_mono f (nextBetting f P n) hc.width_pos hc.left_nonneg hc.right_le_one hst
  have hLR : (n.toOscFrame.eval f).1 ≤ (n.toOscFrame.eval f).2 := (hc.eval_lt f).le
  simp only [childInterp, interp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hLR) (sub_nonneg.mpr hθ)]

theorem continuous_childInterp (n : OscNode) : Continuous (childInterp f P n) :=
  continuous_interp f _ _ _ _

theorem childInterp_left {n : OscNode} :
    childInterp f P n n.interval.left = (n.toOscFrame.eval f).1 := interp_left f _ _ _ _

theorem childInterp_right {n : OscNode} (h : Inv f P n) :
    childInterp f P n n.interval.right = (n.toOscFrame.eval f).2 :=
  interp_right f _ h.connected.width_pos h.connected.left_nonneg h.connected.right_le_one _ _

/-! ## Descendants -/

theorem Inv.of_rawNodeFrom {n d : OscNode} (h : Inv f P n) {path : List OscMove}
    (hd : rawNodeFrom f P n path = some d) : Inv f P d := by
  induction path generalizing n with
  | nil => exact (Option.some.inj hd) ▸ h
  | cons m p ih =>
    rw [rawNodeFrom_cons] at hd
    cases hc : OscNode.step f P n m with
    | none => rw [hc, Option.bind_none] at hd; exact absurd hd (by simp)
    | some c =>
      rw [hc, Option.bind_some] at hd
      exact ih (h.step f P ⟨m, hc⟩) hd

theorem Inv.of_rawNode {d : OscNode} {path : List OscMove} (hd : rawNode f P path = some d) :
    Inv f P d := (Inv.root f P).of_rawNodeFrom f P hd

/-- Descendants sit inside the ancestor, with values inside the ancestor's, and agree with it at a
shared endpoint. -/
theorem descendant_bounds {n d : OscNode} (h : Inv f P n) {path : List OscMove}
    (hd : rawNodeFrom f P n path = some d) :
    d.interval.interval ⊆ n.interval.interval ∧
      (n.toOscFrame.eval f).1 ≤ (d.toOscFrame.eval f).1 ∧
      (d.toOscFrame.eval f).2 ≤ (n.toOscFrame.eval f).2 ∧
      (d.interval.left = n.interval.left → (d.toOscFrame.eval f).1 = (n.toOscFrame.eval f).1) ∧
      (d.interval.right = n.interval.right →
        (d.toOscFrame.eval f).2 = (n.toOscFrame.eval f).2) := by
  induction path generalizing n with
  | nil =>
    obtain rfl := Option.some.inj hd
    exact ⟨le_rfl, le_rfl, le_rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  | cons m p ih =>
    rw [rawNodeFrom_cons] at hd
    cases hc : step f P n m with
    | none => rw [hc, Option.bind_none] at hd; exact absurd hd (by simp)
    | some c =>
      rw [hc, Option.bind_some] at hd
      have hs : Step f P n c := ⟨m, hc⟩
      have hcInv := h.step f P hs
      obtain ⟨hsub, hL, hR, hl, hr⟩ := ih hcInv hd
      have hsub' := hs.interval_subset f P
      obtain ⟨hL', -, hR'⟩ := hs.eval_nested f P h
      obtain ⟨hcL, hcR⟩ := hs.eval_eq_childInterp f P h
      have hcw := hs.width_pos f P h.connected.width_pos
      have hdw := hcInv.of_rawNodeFrom f P hd |>.connected.width_pos
      have hcl := hsub' (Set.left_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
      have hcr := hsub' (Set.right_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
      have hdl := hsub (Set.left_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
      have hdr := hsub (Set.right_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
      refine ⟨hsub.trans hsub', le_trans hL' hL, le_trans hR hR', fun he ↦ ?_, fun he ↦ ?_⟩
      · have hce : c.interval.left = n.interval.left := le_antisymm (by linarith [hdl.1]) hcl.1
        have hdc : d.interval.left = c.interval.left := by rw [he, hce]
        rw [hl hdc, hcL, hce, childInterp_left]
      · have hce : c.interval.right = n.interval.right := le_antisymm hcr.2 (by linarith [hdr.2])
        have hdc : d.interval.right = c.interval.right := by rw [he, hce]
        rw [hr hdc, hcR, hce, childInterp_right f P h]

/-! ## Siblings -/

/-- Distinct children of one node have disjoint interiors. -/
theorem children_disjoint {n c₁ c₂ : OscNode} (h : Inv f P n) {m₁ m₂ : OscMove}
    (h₁ : step f P n m₁ = some c₁) (h₂ : step f P n m₂ = some c₂) (hne : m₁ ≠ m₂) :
    c₁.interval.right ≤ c₂.interval.left ∨ c₂.interval.right ≤ c₁.interval.left := by
  have hw := h.connected.width_pos
  rcases m₁ with b₁ | d₁ <;> rcases m₂ with b₂ | d₂
  · -- two binary children: the two halves
    rw [step_inl, binaryStep_eq] at h₁ h₂
    cases hneed : needsRegrid (nextBetting f P n) n
    · rw [hneed, cond_false] at h₁ h₂
      obtain rfl := Option.some.inj h₁
      obtain rfl := Option.some.inj h₂
      simp only [binaryNode, RatIntervalCode.right, RatIntervalCode.left_child,
        RatIntervalCode.width_child]
      cases b₁ <;> cases b₂
      · exact absurd rfl hne
      · left; simp
      · right; simp
      · exact absurd rfl hne
    · rw [hneed, cond_true] at h₁
      exact absurd h₁ (by simp)
  · -- binary and regridding moves exclude each other
    rw [step_inl, binaryStep_eq] at h₁
    rw [step_inr] at h₂
    cases hneed : needsRegrid (nextBetting f P n) n
    · cases hnb : nextBetting f P n <;> rw [hnb] at h₂ hneed <;>
        simp only [cond_true, cond_false, regridStep_eq, hneed, Bool.false_and] at h₂ <;>
        exact absurd h₂ (by simp)
    · rw [hneed, cond_true] at h₁
      exact absurd h₁ (by simp)
  · rw [step_inl, binaryStep_eq] at h₂
    rw [step_inr] at h₁
    cases hneed : needsRegrid (nextBetting f P n) n
    · cases hnb : nextBetting f P n <;> rw [hnb] at h₁ hneed <;>
        simp only [cond_true, cond_false, regridStep_eq, hneed, Bool.false_and] at h₁ <;>
        exact absurd h₁ (by simp)
    · rw [hneed, cond_true] at h₂
      exact absurd h₂ (by simp)
  · -- two regridding children of the same grid: distinct cells have disjoint interiors
    have hne' : d₁ ≠ d₂ := fun h ↦ hne (by rw [h])
    rw [step_inr] at h₁ h₂
    -- extract the regridding tests and the intervals, uniformly in the resolved state
    have key : ∀ (G : AffineDyadicGrid) (nb : Bool),
        regridStep G nb n d₁ = some c₁ → regridStep G nb n d₂ = some c₂ →
        c₁.interval.right ≤ c₂.interval.left ∨ c₂.interval.right ≤ c₁.interval.left := by
      intro G nb e₁ e₂
      rw [regridStep_eq] at e₁ e₂
      cases t₁ : (needsRegrid nb n && regridChild n.interval G (!nb) d₁)
      · rw [t₁, cond_false] at e₁; exact absurd e₁ (by simp)
      cases t₂ : (needsRegrid nb n && regridChild n.interval G (!nb) d₂)
      · rw [t₂, cond_false] at e₂; exact absurd e₂ (by simp)
      rw [t₁, cond_true] at e₁
      rw [t₂, cond_true] at e₂
      obtain rfl := Option.some.inj e₁
      obtain rfl := Option.some.inj e₂
      rw [Bool.and_eq_true] at t₁ t₂
      simp only [regridNode]
      by_contra hcon
      push Not at hcon
      obtain ⟨hlt₁, hlt₂⟩ := hcon
      have hw₁ := (G.cellCode d₁).width_nonneg
      have hw₂ := (G.cellCode d₂).width_nonneg
      have hpos₁ := G.cellWidth_pos d₁
      have hpos₂ := G.cellWidth_pos d₂
      rw [← AffineDyadicGrid.width_cellCode] at hpos₁ hpos₂
      -- an irrational point in the common interior
      have h11 : (G.cellCode d₁).left < (G.cellCode d₁).right := by
        rw [RatIntervalCode.right]; linarith
      have h22 : (G.cellCode d₂).left < (G.cellCode d₂).right := by
        rw [RatIntervalCode.right]; linarith
      have hlo : max (G.cellCode d₁).left (G.cellCode d₂).left
          < min (G.cellCode d₁).right (G.cellCode d₂).right := by
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨h11, hlt₂⟩, ⟨hlt₁, h22⟩⟩
      obtain ⟨z, hzirr, hz₁, hz₂⟩ := exists_irrational_btwn hlo
      have hz : ∀ q : ℚ, z ≠ (q : ℝ) := fun q hq ↦ hzirr ⟨q, hq.symm⟩
      rw [max_lt_iff] at hz₁
      rw [lt_min_iff] at hz₂
      have hm₁ : z ∈ G.cellInterval d₁ := by
        rw [← AffineDyadicGrid.interval_cellCode]
        exact ⟨hz₁.1.le, hz₂.1.le⟩
      have hm₂ : z ∈ G.cellInterval d₂ := by
        rw [← AffineDyadicGrid.interval_cellCode]
        exact ⟨hz₁.2.le, hz₂.2.le⟩
      exact hne' (regridChild_disjoint_of_ne_rat t₁.2 t₂.2 hz hm₁ hm₂)
    cases hnb : nextBetting f P n <;> rw [hnb] at h₁ h₂ <;>
      simp only [cond_true, cond_false] at h₁ h₂
    · exact key P.waitGrid false h₁ h₂
    · exact key P.betGrid true h₁ h₂

/-! ## Global ordering -/

/-- The coordinate of a side of a node. -/
noncomputable def coord (n : OscNode) (right : Bool) : ℝ :=
  bif right then n.interval.right else n.interval.left

/-- The value at a side of a node. -/
noncomputable def value (n : OscNode) (right : Bool) : ℝ :=
  bif right then (n.toOscFrame.eval f).2 else (n.toOscFrame.eval f).1

theorem coord_mem (n : OscNode) (right : Bool) : coord n right ∈ n.interval.interval := by
  have := n.interval.width_nonneg
  cases right
  · exact Set.left_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith)
  · exact Set.right_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith)

theorem value_mem {n : OscNode} (h : Inv f P n) (right : Bool) :
    (n.toOscFrame.eval f).1 ≤ value f n right ∧ value f n right ≤ (n.toOscFrame.eval f).2 := by
  have := (h.connected.eval_lt f).le
  cases right
  · exact ⟨le_rfl, this⟩
  · exact ⟨this, le_rfl⟩

/-- A side at the ancestor's left endpoint carries the ancestor's left value, and likewise on the
right; a descendant's side cannot sit at the ancestor's far endpoint. -/
private theorem value_of_coord_eq_left {n d : OscNode} (h : Inv f P n) {path : List OscMove}
    (hd : rawNodeFrom f P n path = some d) (s : Bool) (he : coord d s = n.interval.left) :
    value f d s = (n.toOscFrame.eval f).1 := by
  obtain ⟨hsub, -, -, hl, -⟩ := descendant_bounds f P h hd
  have hdw := (h.of_rawNodeFrom f P hd).connected.width_pos
  have hdl := hsub (coord_mem d false)
  have hdr := hsub (coord_mem d true)
  cases s
  · exact hl he
  · exfalso
    have hn : n.interval.right = n.interval.left + n.interval.width := rfl
    have hd' : d.interval.right = d.interval.left + d.interval.width := rfl
    simp only [coord, cond_true, cond_false, RatIntervalCode.interval, Set.mem_Icc] at he hdl hdr
    linarith [hdl.1, hdr.2]

private theorem value_of_coord_eq_right {n d : OscNode} (h : Inv f P n) {path : List OscMove}
    (hd : rawNodeFrom f P n path = some d) (s : Bool) (he : coord d s = n.interval.right) :
    value f d s = (n.toOscFrame.eval f).2 := by
  obtain ⟨hsub, -, -, -, hr⟩ := descendant_bounds f P h hd
  have hdw := (h.of_rawNodeFrom f P hd).connected.width_pos
  have hdl := hsub (coord_mem d false)
  have hdr := hsub (coord_mem d true)
  cases s
  · exfalso
    have hn : n.interval.right = n.interval.left + n.interval.width := rfl
    have hd' : d.interval.right = d.interval.left + d.interval.width := rfl
    simp only [coord, cond_true, cond_false, RatIntervalCode.interval, Set.mem_Icc] at he hdl hdr
    linarith [hdl.1, hdr.2]
  · exact hr he

/-- **Global ordering** from a common node: ordered coordinates have ordered values. -/
theorem value_mono_from {n : OscNode} (h : Inv f P n) (p₁ : List OscMove) :
    ∀ (p₂ : List OscMove) {d₁ d₂ : OscNode} (s₁ s₂ : Bool),
      rawNodeFrom f P n p₁ = some d₁ → rawNodeFrom f P n p₂ = some d₂ →
      coord d₁ s₁ ≤ coord d₂ s₂ → value f d₁ s₁ ≤ value f d₂ s₂ := by
  induction p₁ generalizing n with
  | nil =>
    intro p₂ d₁ d₂ s₁ s₂ h₁ h₂ hle
    obtain rfl := Option.some.inj h₁
    obtain ⟨hsub, hL, hR, -, -⟩ := descendant_bounds f P h h₂
    have hd₂ := hsub (coord_mem d₂ s₂)
    cases s₁
    · exact le_trans hL (value_mem f P (h.of_rawNodeFrom f P h₂) s₂).1
    · have he : coord d₂ s₂ = n.interval.right := le_antisymm hd₂.2 hle
      rw [value_of_coord_eq_right f P h h₂ s₂ he]
      exact le_rfl
  | cons m₁ p₁ ih =>
    intro p₂ d₁ d₂ s₁ s₂ h₁ h₂ hle
    rw [rawNodeFrom_cons] at h₁
    cases hc₁ : step f P n m₁ with
    | none => rw [hc₁, Option.bind_none] at h₁; exact absurd h₁ (by simp)
    | some c₁ =>
    rw [hc₁, Option.bind_some] at h₁
    have hs₁ : Step f P n c₁ := ⟨m₁, hc₁⟩
    have hc₁Inv := h.step f P hs₁
    obtain ⟨hsub₁, hL₁, hR₁, -, -⟩ := descendant_bounds f P hc₁Inv h₁
    cases p₂ with
    | nil =>
      obtain rfl := Option.some.inj h₂
      obtain ⟨hsub, hL, hR, -, -⟩ := descendant_bounds f P h (by
        rw [rawNodeFrom_cons, hc₁, Option.bind_some]; exact h₁)
      have hd₁ := hsub (coord_mem d₁ s₁)
      cases s₂
      · have he : coord d₁ s₁ = n.interval.left := le_antisymm hle hd₁.1
        rw [value_of_coord_eq_left f P h (by rw [rawNodeFrom_cons, hc₁, Option.bind_some]; exact h₁)
          s₁ he]
        exact le_rfl
      · exact le_trans (value_mem f P (h.of_rawNodeFrom f P (by
          rw [rawNodeFrom_cons, hc₁, Option.bind_some]; exact h₁)) s₁).2 hR
    | cons m₂ p₂ =>
      rw [rawNodeFrom_cons] at h₂
      cases hc₂ : step f P n m₂ with
      | none => rw [hc₂, Option.bind_none] at h₂; exact absurd h₂ (by simp)
      | some c₂ =>
      rw [hc₂, Option.bind_some] at h₂
      by_cases hm : m₁ = m₂
      · subst hm
        rw [hc₁] at hc₂
        obtain rfl := Option.some.inj hc₂
        exact ih hc₁Inv p₂ s₁ s₂ h₁ h₂ hle
      have hs₂ : Step f P n c₂ := ⟨m₂, hc₂⟩
      have hc₂Inv := h.step f P hs₂
      obtain ⟨hsub₂, hL₂, hR₂, -, -⟩ := descendant_bounds f P hc₂Inv h₂
      obtain ⟨hcL₁, hcR₁⟩ := hs₁.eval_eq_childInterp f P h
      obtain ⟨hcL₂, hcR₂⟩ := hs₂.eval_eq_childInterp f P h
      have hc₁sub := hs₁.interval_subset f P
      have hc₂sub := hs₂.interval_subset f P
      have hv₁ := value_mem f P (hc₁Inv.of_rawNodeFrom f P h₁) s₁
      have hv₂ := value_mem f P (hc₂Inv.of_rawNodeFrom f P h₂) s₂
      rcases children_disjoint f P h hc₁ hc₂ hm with hord | hord
      · -- `c₁` lies to the left of `c₂`
        have hH : childInterp f P n c₁.interval.right ≤ childInterp f P n c₂.interval.left :=
          childInterp_mono f P h hord
        calc value f d₁ s₁ ≤ (d₁.toOscFrame.eval f).2 := hv₁.2
          _ ≤ (c₁.toOscFrame.eval f).2 := hR₁
          _ = childInterp f P n c₁.interval.right := hcR₁
          _ ≤ childInterp f P n c₂.interval.left := hH
          _ = (c₂.toOscFrame.eval f).1 := hcL₂.symm
          _ ≤ (d₂.toOscFrame.eval f).1 := hL₂
          _ ≤ value f d₂ s₂ := hv₂.1
      · -- `c₂` lies to the left of `c₁`: the coordinates coincide at the shared boundary
        have hd₁ := hsub₁ (coord_mem d₁ s₁)
        have hd₂ := hsub₂ (coord_mem d₂ s₂)
        have he₁ : coord d₁ s₁ = c₁.interval.left := le_antisymm (by linarith [hd₂.2]) hd₁.1
        have he₂ : coord d₂ s₂ = c₂.interval.right := le_antisymm hd₂.2 (by linarith [hd₁.1])
        have hx : c₁.interval.left = c₂.interval.right := by linarith
        rw [value_of_coord_eq_left f P hc₁Inv h₁ s₁ he₁,
          value_of_coord_eq_right f P hc₂Inv h₂ s₂ he₂, hcL₁, hcR₂, hx]

end OscNode

/-! ## Endpoint names -/

/-- An endpoint name: a successful path from the root and a side. -/
structure Endpoint (f : ComputableMonotone) (P : OscillationParams) where
  /-- The path. -/
  path : List OscMove
  /-- The side. -/
  right : Bool
  /-- The node reached. -/
  node : OscNode
  /-- The path succeeds and reaches it. -/
  node_eq : OscNode.rawNode f P path = some node

namespace Endpoint

variable {f : ComputableMonotone} {P : OscillationParams}

/-- The coordinate named. -/
noncomputable def coord (e : Endpoint f P) : ℝ := OscNode.coord e.node e.right

/-- The value assigned. -/
noncomputable def value (e : Endpoint f P) : ℝ := OscNode.value f e.node e.right

theorem inv (e : Endpoint f P) : OscNode.Inv f P e.node := OscNode.Inv.of_rawNode f P e.node_eq

/-- The left endpoint of the root. -/
def rootLeft : Endpoint f P := ⟨[], false, OscNode.root, rfl⟩

/-- The right endpoint of the root. -/
def rootRight : Endpoint f P := ⟨[], true, OscNode.root, rfl⟩

@[simp] theorem coord_rootLeft : (rootLeft : Endpoint f P).coord = 0 := by
  simp [coord, OscNode.coord, rootLeft, OscNode.root, OscFrame.root]

@[simp] theorem value_rootLeft : (rootLeft : Endpoint f P).value = 0 := rfl

@[simp] theorem coord_rootRight : (rootRight : Endpoint f P).coord = 1 := by
  simp [coord, OscNode.coord, rootRight, OscNode.root, OscFrame.root, RatIntervalCode.right]

@[simp] theorem value_rootRight : (rootRight : Endpoint f P).value = 1 := rfl

theorem coord_mem (e : Endpoint f P) : e.coord ∈ e.node.interval.interval :=
  OscNode.coord_mem e.node e.right

theorem coord_mem_unit (e : Endpoint f P) : e.coord ∈ Set.Icc (0 : ℝ) 1 := by
  have hc := e.inv.connected
  have h := e.coord_mem
  rw [RatIntervalCode.interval, Set.mem_Icc] at h
  exact ⟨le_trans hc.left_nonneg h.1, le_trans h.2 hc.right_le_one⟩

theorem value_mem_unit (e : Endpoint f P) : e.value ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h12, h1⟩ := OscValueExpr.orderedUnit_eval f e.node.values
  obtain ⟨hl, hr⟩ := OscNode.value_mem f P e.inv e.right
  exact ⟨le_trans h0 hl, le_trans hr h1⟩

/-- **Global ordering** across branches. -/
theorem value_mono (e₁ e₂ : Endpoint f P) (h : e₁.coord ≤ e₂.coord) : e₁.value ≤ e₂.value :=
  OscNode.value_mono_from f P (OscNode.Inv.root f P) e₁.path e₂.path e₁.right e₂.right
    e₁.node_eq e₂.node_eq h

theorem value_eq_of_coord_eq (e₁ e₂ : Endpoint f P) (h : e₁.coord = e₂.coord) :
    e₁.value = e₂.value :=
  le_antisymm (value_mono e₁ e₂ h.le) (value_mono e₂ e₁ h.ge)

end Endpoint

/-! ## The supremum -/

variable (f : ComputableMonotone) (P : OscillationParams)

/-- The function: the supremum of the values named at or below the argument. Below `0` the family
is empty and the value is `0`; above `1` the root's right endpoint makes it `1`. -/
noncomputable def oscFun (x : ℝ) : ℝ :=
  sSup ((fun e : Endpoint f P ↦ e.value) '' {e | e.coord ≤ x})

namespace oscFun

theorem bddAbove (x : ℝ) : BddAbove ((fun e : Endpoint f P ↦ e.value) '' {e | e.coord ≤ x}) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨e, -, rfl⟩
  exact e.value_mem_unit.2

theorem _root_.AlgorithmicRandomness.Endpoint.value_le_oscFun (e : Endpoint f P) {x : ℝ}
    (hx : e.coord ≤ x) : e.value ≤ oscFun f P x :=
  le_csSup (bddAbove f P x) ⟨e, hx, rfl⟩

theorem le_of_forall {x b : ℝ} (hx : 0 ≤ x) (hb : ∀ e : Endpoint f P, e.coord ≤ x → e.value ≤ b) :
    oscFun f P x ≤ b := by
  refine csSup_le ⟨_, Endpoint.rootLeft, by simpa using hx, rfl⟩ ?_
  rintro _ ⟨e, he, rfl⟩
  exact hb e he

theorem of_neg {x : ℝ} (hx : x < 0) : oscFun f P x = 0 := by
  have h : {e : Endpoint f P | e.coord ≤ x} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx e.coord_mem_unit.1
  rw [oscFun, h, Set.image_empty, Real.sSup_empty]

theorem nonneg (x : ℝ) : 0 ≤ oscFun f P x := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [of_neg f P hx]
  · simpa using Endpoint.rootLeft.value_le_oscFun f P (x := x) (by simpa using hx)

theorem le_one (x : ℝ) : oscFun f P x ≤ 1 := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [of_neg f P hx]; exact zero_le_one
  · exact le_of_forall f P hx fun e _ ↦ e.value_mem_unit.2

theorem mem_unit (x : ℝ) : oscFun f P x ∈ Set.Icc (0 : ℝ) 1 := ⟨nonneg f P x, le_one f P x⟩

/-- Exact agreement at every named endpoint. -/
theorem endpoint (e : Endpoint f P) : oscFun f P e.coord = e.value :=
  le_antisymm (le_of_forall f P e.coord_mem_unit.1 fun e' h ↦ e'.value_mono e h)
    (e.value_le_oscFun f P le_rfl)

theorem monotone : Monotone (oscFun f P) := by
  intro x y hxy
  rcases lt_or_ge x 0 with hx | hx
  · rw [of_neg f P hx]; exact nonneg f P y
  · exact le_of_forall f P hx fun e he ↦ e.value_le_oscFun f P (le_trans he hxy)

theorem le_of_le_coord (e : Endpoint f P) {x : ℝ} (hx : x ≤ e.coord) : oscFun f P x ≤ e.value := by
  rcases lt_or_ge x 0 with hx0 | hx0
  · rw [of_neg f P hx0]; exact e.value_mem_unit.1
  · exact le_of_forall f P hx0 fun e' he' ↦ e'.value_mono e (le_trans he' hx)

theorem of_one_le {x : ℝ} (hx : 1 ≤ x) : oscFun f P x = 1 :=
  le_antisymm (le_one f P x)
    (by simpa using Endpoint.rootRight.value_le_oscFun f P (x := x) (by simpa using hx))

@[simp] theorem zero : oscFun f P 0 = 0 := by
  simpa using endpoint f P Endpoint.rootLeft

@[simp] theorem one : oscFun f P 1 = 1 := by
  simpa using endpoint f P Endpoint.rootRight

end oscFun

/-! ## Density -/

namespace OscNode

theorem step_inr_eq {n : OscNode} {c : AffineDyadicCell}
    (hneed : needsRegrid (nextBetting f P n) n = true)
    (hreg : regridChild n.interval (gridOf P (nextBetting f P n)) (!nextBetting f P n) c = true) :
    step f P n (Sum.inr c)
      = some (regridNode (gridOf P (nextBetting f P n)) (nextBetting f P n) n c) := by
  rw [step_inr]
  cases hnb : nextBetting f P n
  · rw [hnb] at hneed hreg
    rw [cond_false]
    change regridStep (gridOf P false) false n c = _
    rw [regridStep_eq, hneed, hreg]
    rfl
  · rw [hnb] at hneed hreg
    rw [cond_true]
    change regridStep (gridOf P true) true n c = _
    rw [regridStep_eq, hneed, hreg]
    rfl

theorem step_inl_eq {n : OscNode} (hneed : needsRegrid (nextBetting f P n) n = false) (b : Bool) :
    step f P n (Sum.inl b) = some (binaryNode n b) := by
  rw [step_inl, binaryStep_eq, hneed, cond_false]

/-- Every irrational point of a node's interval lies in some child. -/
theorem exists_step_mem {n : OscNode} {x : ℝ} (hx : x ∈ n.interval.interval)
    (hirr : ∀ q : ℚ, x ≠ (q : ℝ)) : ∃ c, Step f P n c ∧ x ∈ c.interval.interval := by
  cases hneed : needsRegrid (nextBetting f P n) n
  · -- binary children cover everything
    rw [RatIntervalCode.interval, Set.mem_Icc, RatIntervalCode.right] at hx
    rcases le_or_gt x (n.interval.left + n.interval.width / 2) with hle | hgt
    · refine ⟨binaryNode n false, ⟨Sum.inl false, step_inl_eq f P hneed false⟩, ?_⟩
      simp only [binaryNode, RatIntervalCode.interval, Set.mem_Icc, RatIntervalCode.right,
        RatIntervalCode.left_child, RatIntervalCode.width_child]
      rw [if_neg Bool.false_ne_true]
      constructor <;> linarith
    · refine ⟨binaryNode n true, ⟨Sum.inl true, step_inl_eq f P hneed true⟩, ?_⟩
      simp only [binaryNode, RatIntervalCode.interval, Set.mem_Icc, RatIntervalCode.right,
        RatIntervalCode.left_child, RatIntervalCode.width_child]
      rw [if_pos trivial]
      constructor <;> linarith
  · obtain ⟨c, hreg, hmem⟩ := exists_regridChild_of_mem_of_ne_rat n.interval
      (gridOf P (nextBetting f P n)) (!nextBetting f P n) hirr hx
    refine ⟨_, ⟨Sum.inr c, step_inr_eq f P hneed hreg⟩, ?_⟩
    simp only [regridNode]
    rw [AffineDyadicGrid.interval_cellCode]
    exact hmem

/-- The chain of nodes through an irrational point, chosen classically at each step. -/
noncomputable def irrationalChain {x : ℝ} (hirr : ∀ q : ℚ, x ≠ (q : ℝ))
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : ℕ → {n : OscNode // Inv f P n ∧ x ∈ n.interval.interval}
  | 0 => ⟨root, Inv.root f P, by simpa [root, OscFrame.root] using hx⟩
  | k + 1 =>
    let p := irrationalChain hirr hx k
    ⟨Classical.choose (exists_step_mem f P p.2.2 hirr),
      p.2.1.step f P (Classical.choose_spec (exists_step_mem f P p.2.2 hirr)).1,
      (Classical.choose_spec (exists_step_mem f P p.2.2 hirr)).2⟩

theorem irrationalChain_step {x : ℝ} (hirr : ∀ q : ℚ, x ≠ (q : ℝ)) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) : Step f P (irrationalChain f P hirr hx k).1 (irrationalChain f P hirr hx (k + 1)).1 :=
  (Classical.choose_spec (exists_step_mem f P (irrationalChain f P hirr hx k).2.2 hirr)).1

/-- Every irrational point of the unit interval lies on an infinite path. -/
theorem exists_oscPath_mem {x : ℝ} (hirr : ∀ q : ℚ, x ≠ (q : ℝ)) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ γ : OscPath f P, ∀ k, x ∈ (γ.node k).interval.interval :=
  ⟨⟨fun k ↦ (irrationalChain f P hirr hx k).1, rfl, irrationalChain_step f P hirr hx⟩,
    fun k ↦ (irrationalChain f P hirr hx k).2.2⟩

end OscNode

namespace OscPath

variable {f P}

theorem exists_path (γ : OscPath f P) (k : ℕ) :
    ∃ p : List OscMove, OscNode.rawNode f P p = some (γ.node k) := by
  induction k with
  | zero => exact ⟨[], by rw [OscNode.rawNode_nil, γ.node_zero]⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨m, hm⟩ := γ.step k
    exact ⟨p ++ [m], by rw [OscNode.rawNode_append_singleton, hp, Option.bind_some, hm]⟩

end OscPath

/-- Endpoints are dense in the unit interval. -/
theorem exists_endpoint_mem_Ioo {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∃ e : Endpoint f P, e.coord ∈ Set.Ioo a b := by
  obtain ⟨z, hzirr, hz⟩ := exists_irrational_btwn hab
  have hirr : ∀ q : ℚ, z ≠ (q : ℝ) := fun q hq ↦ hzirr ⟨q, hq.symm⟩
  obtain ⟨γ, hγ⟩ := OscNode.exists_oscPath_mem f P hirr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hsmall : ∀ᶠ k in atTop, (γ.node k).interval.width < z - a :=
    (tendsto_order.1 γ.width_tendsto_zero).2 _ (by linarith [hz.1])
  obtain ⟨k, hk⟩ := hsmall.exists
  obtain ⟨p, hp⟩ := γ.exists_path k
  refine ⟨⟨p, false, γ.node k, hp⟩, ?_⟩
  have hm := hγ k
  rw [RatIntervalCode.interval, Set.mem_Icc, RatIntervalCode.right] at hm
  simp only [Endpoint.coord, OscNode.coord, cond_false, Set.mem_Ioo]
  constructor <;> linarith [hz.1, hz.2]

/-! ## Continuity

At a *stopped* point — one lying in no child's interior — the function agrees with the parent's
continuous interpolation, which then controls it from both sides. Along a chain that never stops
the mass tends to zero. -/

namespace OscNode

/-- A child endpoint, named through the parent's path. -/
def childEndpoint {p : List OscMove} {n c : OscNode} (hn : rawNode f P p = some n) {m : OscMove}
    (hm : step f P n m = some c) (right : Bool) : Endpoint f P :=
  ⟨p ++ [m], right, c, by rw [rawNode_append_singleton, hn, Option.bind_some, hm]⟩

/-- At a point of the parent that lies in no child's interior, the function is the parent's
interpolation. -/
theorem oscFun_eq_childInterp {p : List OscMove} {n : OscNode} (hn : rawNode f P p = some n)
    {x : ℝ} (hx : x ∈ n.interval.interval)
    (hstop : ∀ c, Step f P n c → x ∉ Set.Ioo c.interval.left c.interval.right) :
    oscFun f P x = childInterp f P n x := by
  have h := Inv.of_rawNode f P hn
  have hcont := (continuous_childInterp f P n).continuousAt (x := x)
  rw [Metric.continuousAt_iff] at hcont
  have hxI := hx
  rw [RatIntervalCode.interval, Set.mem_Icc] at hxI
  refine le_antisymm ?_ ?_
  · -- from the right
    rcases eq_or_lt_of_le hxI.2 with hxr | hxr
    · have he := oscFun.endpoint f P ⟨p, true, n, hn⟩
      simp only [Endpoint.coord, Endpoint.value, coord, value, cond_true] at he
      rw [hxr, he, childInterp_right f P h]
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    obtain ⟨ε, hε, hεH⟩ := hcont δ hδ
    obtain ⟨z, hzirr, hz₁, hz₂⟩ := exists_irrational_btwn
      (show x < min (x + ε) n.interval.right from lt_min (by linarith) hxr)
    rw [lt_min_iff] at hz₂
    have hirr : ∀ q : ℚ, z ≠ (q : ℝ) := fun q hq ↦ hzirr ⟨q, hq.symm⟩
    obtain ⟨c, ⟨m, hm⟩, hzc⟩ := exists_step_mem f P (x := z) ⟨by linarith, hz₂.2.le⟩ hirr
    rw [RatIntervalCode.interval, Set.mem_Icc] at hzc
    have hxc : x ≤ c.interval.left := by
      by_contra hlt
      push Not at hlt
      exact hstop c ⟨m, hm⟩ ⟨hlt, by linarith⟩
    have hle := oscFun.le_of_le_coord f P (childEndpoint f P hn hm false) (x := x) hxc
    simp only [Endpoint.value, childEndpoint, value, cond_false] at hle
    rw [(Step.eval_eq_childInterp f P h ⟨m, hm⟩).1] at hle
    have hclose := hεH (show dist c.interval.left x < ε by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at hclose
    linarith
  · -- from the left
    rcases eq_or_lt_of_le hxI.1 with hxl | hxl
    · have he := oscFun.endpoint f P ⟨p, false, n, hn⟩
      simp only [Endpoint.coord, Endpoint.value, coord, value, cond_false] at he
      rw [← hxl, he, childInterp_left]
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    obtain ⟨ε, hε, hεH⟩ := hcont δ hδ
    obtain ⟨z, hzirr, hz₁, hz₂⟩ := exists_irrational_btwn
      (show max (x - ε) n.interval.left < x from max_lt (by linarith) hxl)
    rw [max_lt_iff] at hz₁
    have hirr : ∀ q : ℚ, z ≠ (q : ℝ) := fun q hq ↦ hzirr ⟨q, hq.symm⟩
    obtain ⟨c, ⟨m, hm⟩, hzc⟩ := exists_step_mem f P (x := z) ⟨hz₁.2.le, by linarith⟩ hirr
    rw [RatIntervalCode.interval, Set.mem_Icc] at hzc
    have hxc : c.interval.right ≤ x := by
      by_contra hlt
      push Not at hlt
      exact hstop c ⟨m, hm⟩ ⟨by linarith, hlt⟩
    have hle := (childEndpoint f P hn hm true).value_le_oscFun f P (x := x) hxc
    simp only [Endpoint.value, childEndpoint, value, cond_true] at hle
    rw [(Step.eval_eq_childInterp f P h ⟨m, hm⟩).2] at hle
    have hclose := hεH (show dist c.interval.right x < ε by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at hclose
    linarith

/-- The right gap lemma: at a stopped point below the parent's right endpoint, children's left
endpoints approach from the right. -/
theorem exists_child_left_near {n : OscNode} {x : ℝ} (hx : x ∈ n.interval.interval)
    (hxr : x < n.interval.right)
    (hstop : ∀ c, Step f P n c → x ∉ Set.Ico c.interval.left c.interval.right) {ε : ℝ}
    (hε : 0 < ε) : ∃ c, Step f P n c ∧ x < c.interval.left ∧ c.interval.left < x + ε := by
  obtain ⟨z, hzirr, hz₁, hz₂⟩ := exists_irrational_btwn
    (show x < min (x + ε) n.interval.right from lt_min (by linarith) hxr)
  rw [lt_min_iff] at hz₂
  have hirr : ∀ q : ℚ, z ≠ (q : ℝ) := fun q hq ↦ hzirr ⟨q, hq.symm⟩
  have hxI := hx
  rw [RatIntervalCode.interval, Set.mem_Icc] at hxI
  obtain ⟨c, hs, hzc⟩ := exists_step_mem f P (x := z) ⟨by linarith, hz₂.2.le⟩ hirr
  rw [RatIntervalCode.interval, Set.mem_Icc] at hzc
  refine ⟨c, hs, ?_, by linarith⟩
  by_contra hle
  push Not at hle
  exact hstop c hs ⟨hle, by linarith⟩

/-- The left gap lemma. -/
theorem exists_child_right_near {n : OscNode} {x : ℝ} (hx : x ∈ n.interval.interval)
    (hxl : n.interval.left < x)
    (hstop : ∀ c, Step f P n c → x ∉ Set.Ioc c.interval.left c.interval.right) {ε : ℝ}
    (hε : 0 < ε) : ∃ c, Step f P n c ∧ x - ε < c.interval.right ∧ c.interval.right < x := by
  obtain ⟨z, hzirr, hz₁, hz₂⟩ := exists_irrational_btwn
    (show max (x - ε) n.interval.left < x from max_lt (by linarith) hxl)
  rw [max_lt_iff] at hz₁
  have hirr : ∀ q : ℚ, z ≠ (q : ℝ) := fun q hq ↦ hzirr ⟨q, hq.symm⟩
  have hxI := hx
  rw [RatIntervalCode.interval, Set.mem_Icc] at hxI
  obtain ⟨c, hs, hzc⟩ := exists_step_mem f P (x := z) ⟨hz₁.2.le, by linarith⟩ hirr
  rw [RatIntervalCode.interval, Set.mem_Icc] at hzc
  refine ⟨c, hs, by linarith, ?_⟩
  by_contra hle
  push Not at hle
  exact hstop c hs ⟨by linarith, hle⟩

/-! ### Selected chains -/

/-- A reachable node satisfying a selection predicate, with its path. -/
structure Sel (S : OscNode → Prop) where
  /-- The path. -/
  path : List OscMove
  /-- The node. -/
  node : OscNode
  /-- Reachability. -/
  node_eq : rawNode f P path = some node
  /-- The selection. -/
  sel : S node

open scoped Classical in
/-- The next selected child, if any; otherwise the node itself. -/
noncomputable def Sel.next {S : OscNode → Prop} (q : Sel f P S) : Sel f P S :=
  if h : ∃ (m : OscMove) (c : OscNode), step f P q.node m = some c ∧ S c then
    ⟨q.path ++ [Classical.choose h], Classical.choose (Classical.choose_spec h), by
      rw [rawNode_append_singleton, q.node_eq, Option.bind_some]
      exact (Classical.choose_spec (Classical.choose_spec h)).1,
      (Classical.choose_spec (Classical.choose_spec h)).2⟩
  else q

/-- The chain of selected nodes from a start. -/
noncomputable def selChain {S : OscNode → Prop} (start : Sel f P S) : ℕ → Sel f P S
  | 0 => start
  | k + 1 => (selChain start k).next

theorem Sel.next_step {S : OscNode → Prop} (q : Sel f P S)
    (h : ∃ (m : OscMove) (c : OscNode), step f P q.node m = some c ∧ S c) :
    Step f P q.node q.next.node := by
  rw [Sel.next, dif_pos h]
  exact ⟨_, (Classical.choose_spec (Classical.choose_spec h)).1⟩

theorem Sel.next_eq_of_stopped {S : OscNode → Prop} (q : Sel f P S)
    (h : ¬ ∃ (m : OscMove) (c : OscNode), step f P q.node m = some c ∧ S c) :
    q.next = q := by
  rw [Sel.next, dif_neg h]

/-- Either the chain continues forever, or some node of it is stopped. -/
theorem selChain_forever_or_stopped {S : OscNode → Prop} (start : Sel f P S) :
    (∀ k, Step f P (selChain f P start k).node (selChain f P start (k + 1)).node) ∨
      ∃ k, ∀ c, Step f P (selChain f P start k).node c → ¬ S c := by
  by_cases hall : ∀ k, ∃ (m : OscMove) (c : OscNode),
      step f P (selChain f P start k).node m = some c ∧ S c
  · exact Or.inl fun k ↦ Sel.next_step f P _ (hall k)
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    exact Or.inr ⟨k, fun c ⟨m, hm⟩ hS ↦ hk m c hm hS⟩

/-- The root as a selected start. -/
def Sel.root {S : OscNode → Prop} (h : S OscNode.root) : Sel f P S := ⟨[], OscNode.root, rfl, h⟩

/-- The path through a forever-continuing chain from the root. -/
noncomputable def selPath {S : OscNode → Prop} (h : S OscNode.root)
    (hall : ∀ k, Step f P (selChain f P (Sel.root f P h) k).node
      (selChain f P (Sel.root f P h) (k + 1)).node) : OscPath f P :=
  ⟨fun k ↦ (selChain f P (Sel.root f P h) k).node, rfl, hall⟩

/-! ### One-sided continuity -/

theorem oscFun_continuousWithinAt_Ici {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousWithinAt (oscFun f P) (Set.Ici x) x := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hroot : x ∈ Set.Ico root.interval.left root.interval.right := by
    simpa [root, OscFrame.root, RatIntervalCode.right] using hx
  set S : OscNode → Prop := fun c ↦ x ∈ Set.Ico c.interval.left c.interval.right with hS
  rcases selChain_forever_or_stopped f P (Sel.root f P (S := S) hroot) with hall | ⟨k, hstop⟩
  · -- the chain never stops: the mass tends to zero
    set γ := selPath f P hroot hall with hγ
    obtain ⟨k, hk⟩ := ((tendsto_order.1 γ.mass_tendsto_zero).2 ε hε).exists
    set q := selChain f P (Sel.root f P (S := S) hroot) k with hq
    have hxq : x ∈ Set.Ico q.node.interval.left q.node.interval.right := q.sel
    refine ⟨q.node.interval.right - x, by linarith [hxq.2], fun y hy hyx ↦ ?_⟩
    rw [Set.mem_Ici] at hy
    rw [Real.dist_eq, abs_lt] at hyx
    have h1 := oscFun.le_of_le_coord f P ⟨q.path, true, q.node, q.node_eq⟩ (x := y)
      (by simp only [Endpoint.coord, coord, cond_true]; linarith)
    have h2 := (⟨q.path, false, q.node, q.node_eq⟩ : Endpoint f P).value_le_oscFun f P (x := x)
      (by simp only [Endpoint.coord, coord, cond_false]; exact hxq.1)
    have h3 := oscFun.monotone f P hy
    simp only [Endpoint.value, value, cond_true, cond_false] at h1 h2
    have hmass : (q.node.toOscFrame.eval f).2 - (q.node.toOscFrame.eval f).1 < ε := hk
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · -- stopped: the parent's interpolation controls the right side
    set q := selChain f P (Sel.root f P (S := S) hroot) k with hq
    have hxq : x ∈ Set.Ico q.node.interval.left q.node.interval.right := q.sel
    have hxI : x ∈ q.node.interval.interval := ⟨hxq.1, hxq.2.le⟩
    have hstop' : ∀ c, Step f P q.node c → x ∉ Set.Ioo c.interval.left c.interval.right :=
      fun c hc hmem ↦ hstop c hc ⟨hmem.1.le, hmem.2⟩
    have hagree := oscFun_eq_childInterp f P q.node_eq hxI hstop'
    have hcont := (continuous_childInterp f P q.node).continuousAt (x := x)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨ε', hε', hεH⟩ := hcont ε hε
    obtain ⟨c, ⟨m, hm⟩, hcl, hcl'⟩ := exists_child_left_near f P hxI hxq.2 hstop hε'
    refine ⟨c.interval.left - x, by linarith, fun y hy hyx ↦ ?_⟩
    rw [Set.mem_Ici] at hy
    rw [Real.dist_eq, abs_lt] at hyx
    have h1 := oscFun.le_of_le_coord f P (childEndpoint f P q.node_eq hm false) (x := y)
      (by simp only [Endpoint.coord, childEndpoint, coord, cond_false]; linarith)
    simp only [Endpoint.value, childEndpoint, value, cond_false] at h1
    rw [(Step.eval_eq_childInterp f P (Inv.of_rawNode f P q.node_eq) ⟨m, hm⟩).1] at h1
    have hclose := hεH (show dist c.interval.left x < ε' by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at hclose
    have h3 := oscFun.monotone f P hy
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

theorem oscFun_continuousWithinAt_Iic {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ContinuousWithinAt (oscFun f P) (Set.Iic x) x := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hroot : x ∈ Set.Ioc root.interval.left root.interval.right := by
    simpa [root, OscFrame.root, RatIntervalCode.right] using hx
  set S : OscNode → Prop := fun c ↦ x ∈ Set.Ioc c.interval.left c.interval.right with hS
  rcases selChain_forever_or_stopped f P (Sel.root f P (S := S) hroot) with hall | ⟨k, hstop⟩
  · set γ := selPath f P hroot hall with hγ
    obtain ⟨k, hk⟩ := ((tendsto_order.1 γ.mass_tendsto_zero).2 ε hε).exists
    set q := selChain f P (Sel.root f P (S := S) hroot) k with hq
    have hxq : x ∈ Set.Ioc q.node.interval.left q.node.interval.right := q.sel
    refine ⟨x - q.node.interval.left, by linarith [hxq.1], fun y hy hyx ↦ ?_⟩
    rw [Set.mem_Iic] at hy
    rw [Real.dist_eq, abs_lt] at hyx
    have h1 := oscFun.le_of_le_coord f P ⟨q.path, true, q.node, q.node_eq⟩ (x := x)
      (by simp only [Endpoint.coord, coord, cond_true]; exact hxq.2)
    have h2 := (⟨q.path, false, q.node, q.node_eq⟩ : Endpoint f P).value_le_oscFun f P (x := y)
      (by simp only [Endpoint.coord, coord, cond_false]; linarith)
    have h3 := oscFun.monotone f P hy
    simp only [Endpoint.value, value, cond_true, cond_false] at h1 h2
    have hmass : (q.node.toOscFrame.eval f).2 - (q.node.toOscFrame.eval f).1 < ε := hk
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · set q := selChain f P (Sel.root f P (S := S) hroot) k with hq
    have hxq : x ∈ Set.Ioc q.node.interval.left q.node.interval.right := q.sel
    have hxI : x ∈ q.node.interval.interval := ⟨hxq.1.le, hxq.2⟩
    have hstop' : ∀ c, Step f P q.node c → x ∉ Set.Ioo c.interval.left c.interval.right :=
      fun c hc hmem ↦ hstop c hc ⟨hmem.1, hmem.2.le⟩
    have hagree := oscFun_eq_childInterp f P q.node_eq hxI hstop'
    have hcont := (continuous_childInterp f P q.node).continuousAt (x := x)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨ε', hε', hεH⟩ := hcont ε hε
    obtain ⟨c, ⟨m, hm⟩, hcr, hcr'⟩ := exists_child_right_near f P hxI hxq.1 hstop hε'
    refine ⟨x - c.interval.right, by linarith, fun y hy hyx ↦ ?_⟩
    rw [Set.mem_Iic] at hy
    rw [Real.dist_eq, abs_lt] at hyx
    have h1 := (childEndpoint f P q.node_eq hm true).value_le_oscFun f P (x := y)
      (by simp only [Endpoint.coord, childEndpoint, coord, cond_true]; linarith)
    simp only [Endpoint.value, childEndpoint, value, cond_true] at h1
    rw [(Step.eval_eq_childInterp f P (Inv.of_rawNode f P q.node_eq) ⟨m, hm⟩).2] at h1
    have hclose := hεH (show dist c.interval.right x < ε' by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at hclose
    have h3 := oscFun.monotone f P hy
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

end OscNode

/-- **Continuity** of the oscillating function on the unit interval. -/
theorem oscFun_continuousOn : ContinuousOn (oscFun f P) (Set.Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst h0
    exact (OscNode.oscFun_continuousWithinAt_Ici f P ⟨le_rfl, zero_lt_one⟩).mono fun y hy ↦ hy.1
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1
    exact (OscNode.oscFun_continuousWithinAt_Iic f P ⟨h0, le_rfl⟩).mono fun y hy ↦ hy.2
  refine ((OscNode.oscFun_continuousWithinAt_Ici f P ⟨hx.1, h1⟩).union
    (OscNode.oscFun_continuousWithinAt_Iic f P ⟨h0, hx.2⟩)).mono fun y _ ↦ ?_
  rcases le_total x y with h | h
  · exact Or.inl h
  · exact Or.inr h


/-! ## The approximation program

The program searches for a certified bracket: two names around the clamped argument whose coded
values at precision `j` differ by at most `3 · 2⁻ʲ`. Global ordering makes the certificate sound;
density and continuity make the search terminate. The argument itself need not be an endpoint. -/

/-- A bracket candidate: two names, each a path with a side. -/
abbrev OscBracket := (List OscMove × Bool) × (List OscMove × Bool)

namespace OscNode

/-- The coded coordinate of a side. -/
def sideCode (n : OscNode) (right : Bool) : ℕ :=
  bif right then n.interval.rightCode else n.interval.leftCode

theorem primrec_sideCode : Primrec₂ sideCode :=
  Primrec.cond Primrec.snd
    (primrec_ratIntervalCode_rightCode.comp (primrec_interval.comp Primrec.fst))
    (primrec_ratIntervalCode_leftCode.comp (primrec_interval.comp Primrec.fst))

theorem value_sideCode (n : OscNode) (right : Bool) :
    ((RatCode.value (sideCode n right) : ℚ) : ℝ) = coord n right := by
  cases right
  · rfl
  · simp only [sideCode, coord, cond_true]
    exact RatIntervalCode.value_rightCode _

/-- The coded value of a side at precision `j`. -/
noncomputable def sideValueCode (n : OscNode) (right : Bool) (j : ℕ) : ℕ :=
  bif right then (OscValueExpr.evalCode f n.values j).2 else (OscValueExpr.evalCode f n.values j).1

theorem computable_sideValueCode :
    Computable fun q : OscNode × Bool × ℕ ↦ sideValueCode f q.1 q.2.1 q.2.2 := by
  have heval : Computable fun q : OscNode × Bool × ℕ ↦ OscValueExpr.evalCode f q.1.values q.2.2 :=
    (OscValueExpr.computable_evalCode f).comp
      (primrec_values.to_comp.comp Computable.fst) (Computable.snd.comp Computable.snd)
  exact (Computable.cond (Computable.fst.comp Computable.snd) (Computable.snd.comp heval)
    (Computable.fst.comp heval)).of_eq fun _ ↦ rfl

theorem sideValueCode_le_one (n : OscNode) (right : Bool) (j : ℕ) :
    NNRatCode.value (sideValueCode f n right j) ≤ 1 := by
  have h := OscValueExpr.approx_evalCode f n.values j
  cases right
  · exact h.1
  · exact h.2.1

theorem sideValueCode_error (n : OscNode) (right : Bool) (j : ℕ) :
    |((NNRatCode.value (sideValueCode f n right j) : ℚ) : ℝ) - value f n right|
      ≤ (2⁻¹ : ℝ) ^ j := by
  have h := OscValueExpr.approx_evalCode f n.values j
  cases right
  · exact h.2.2.1
  · exact h.2.2.2

end OscNode

-- From here on the recursion and the side values are used only through their contracts.
attribute [local irreducible] OscNode.rawNode OscNode.rawNodeFrom OscNode.step
  OscNode.sideValueCode

/-- The gap bound `3 · 2⁻ʲ`, as a nonnegative code. -/
def oscGapCode (j : ℕ) : ℕ := NNRatCode.divPowTwo j (NNRatCode.ofNat 3)

theorem value_oscGapCode (j : ℕ) :
    ((NNRatCode.value (oscGapCode j) : ℚ) : ℝ) = 3 * (2⁻¹ : ℝ) ^ j := by
  rw [oscGapCode, NNRatCode.value_divPowTwo, NNRatCode.value_ofNat]
  push_cast
  rw [inv_pow]
  ring

/-- The certificate: both paths succeed, the coordinates bracket the clamped argument, and the
coded values differ by at most the gap. -/
noncomputable def oscBracketOk (q j : ℕ) (b : OscBracket) : Bool :=
  match OscNode.rawNode f P b.1.1, OscNode.rawNode f P b.2.1 with
  | some n₁, some n₂ =>
    RatCode.le (OscNode.sideCode n₁ b.1.2) (RatCode.ofNNRat (RatCode.clampUnit q))
      && RatCode.le (RatCode.ofNNRat (RatCode.clampUnit q)) (OscNode.sideCode n₂ b.2.2)
      && NNRatCode.le (NNRatCode.sub (OscNode.sideValueCode f n₂ b.2.2 j)
          (OscNode.sideValueCode f n₁ b.1.2 j)) (oscGapCode j)
      && NNRatCode.le (NNRatCode.sub (OscNode.sideValueCode f n₁ b.1.2 j)
          (OscNode.sideValueCode f n₂ b.2.2 j)) (oscGapCode j)
  | _, _ => false

theorem computable_oscBracketOk :
    Computable fun t : (ℕ × ℕ) × OscBracket ↦ oscBracketOk f P t.1.1 t.1.2 t.2 := by
  -- the body, on `((q, j), b)` together with the two nodes
  have hq : Primrec fun t : (ℕ × ℕ) × OscBracket ↦ t.1.1 := Primrec.fst.comp Primrec.fst
  have hj : Primrec fun t : (ℕ × ℕ) × OscBracket ↦ t.1.2 := Primrec.snd.comp Primrec.fst
  have hp₁ : Primrec fun t : (ℕ × ℕ) × OscBracket ↦ t.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hs₁ : Primrec fun t : (ℕ × ℕ) × OscBracket ↦ t.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hp₂ : Primrec fun t : (ℕ × ℕ) × OscBracket ↦ t.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs₂ : Primrec fun t : (ℕ × ℕ) × OscBracket ↦ t.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hr₁ := (OscNode.computable_rawNode f P).comp hp₁.to_comp
  have hr₂ := (OscNode.computable_rawNode f P).comp hp₂.to_comp
  -- inner body on `(t, n₁) × n₂`
  have hbody : Computable₂ fun (u : ((ℕ × ℕ) × OscBracket) × OscNode) (n₂ : OscNode) ↦
      (RatCode.le (OscNode.sideCode u.2 u.1.2.1.2) (RatCode.ofNNRat (RatCode.clampUnit u.1.1.1))
        && RatCode.le (RatCode.ofNNRat (RatCode.clampUnit u.1.1.1)) (OscNode.sideCode n₂ u.1.2.2.2)
        && NNRatCode.le (NNRatCode.sub (OscNode.sideValueCode f n₂ u.1.2.2.2 u.1.1.2)
            (OscNode.sideValueCode f u.2 u.1.2.1.2 u.1.1.2)) (oscGapCode u.1.1.2)
        && NNRatCode.le (NNRatCode.sub (OscNode.sideValueCode f u.2 u.1.2.1.2 u.1.1.2)
            (OscNode.sideValueCode f n₂ u.1.2.2.2 u.1.1.2)) (oscGapCode u.1.1.2)) := by
    have ht : Primrec fun w : (((ℕ × ℕ) × OscBracket) × OscNode) × OscNode ↦ w.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hn₁ : Primrec fun w : (((ℕ × ℕ) × OscBracket) × OscNode) × OscNode ↦ w.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hn₂ : Primrec fun w : (((ℕ × ℕ) × OscBracket) × OscNode) × OscNode ↦ w.2 := Primrec.snd
    have hx := RatCode.primrec_ofNNRat.comp (RatCode.primrec_clampUnit.comp (hq.comp ht))
    have hgap : Primrec fun w : (((ℕ × ℕ) × OscBracket) × OscNode) × OscNode ↦
        oscGapCode w.1.1.1.2 :=
      NNRatCode.primrec_divPowTwo.comp (hj.comp ht) (Primrec.const _)
    have hc₁ := OscNode.primrec_sideCode.comp hn₁ (hs₁.comp ht)
    have hc₂ := OscNode.primrec_sideCode.comp hn₂ (hs₂.comp ht)
    have hv₁ := (OscNode.computable_sideValueCode f).comp
      (hn₁.pair ((hs₁.comp ht).pair (hj.comp ht))).to_comp
    have hv₂ := (OscNode.computable_sideValueCode f).comp
      (hn₂.pair ((hs₂.comp ht).pair (hj.comp ht))).to_comp
    have h1 := (RatCode.primrec_le.comp hc₁ hx).to_comp
    have h2 := (RatCode.primrec_le.comp hx hc₂).to_comp
    have h3 := NNRatCode.primrec_le.to_comp.comp (NNRatCode.primrec_sub.to_comp.comp hv₂ hv₁)
      hgap.to_comp
    have h4 := NNRatCode.primrec_le.to_comp.comp (NNRatCode.primrec_sub.to_comp.comp hv₁ hv₂)
      hgap.to_comp
    exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp h1 h2) h3)
      h4).of_eq fun _ ↦ rfl
  have hinner : Computable₂ fun (t : (ℕ × ℕ) × OscBracket) (n₁ : OscNode) ↦
      Option.casesOn (motive := fun _ ↦ Bool) (OscNode.rawNode f P t.2.2.1) false
        (fun n₂ ↦ (RatCode.le (OscNode.sideCode n₁ t.2.1.2)
            (RatCode.ofNNRat (RatCode.clampUnit t.1.1))
          && RatCode.le (RatCode.ofNNRat (RatCode.clampUnit t.1.1)) (OscNode.sideCode n₂ t.2.2.2)
          && NNRatCode.le (NNRatCode.sub (OscNode.sideValueCode f n₂ t.2.2.2 t.1.2)
              (OscNode.sideValueCode f n₁ t.2.1.2 t.1.2)) (oscGapCode t.1.2)
          && NNRatCode.le (NNRatCode.sub (OscNode.sideValueCode f n₁ t.2.1.2 t.1.2)
              (OscNode.sideValueCode f n₂ t.2.2.2 t.1.2)) (oscGapCode t.1.2))) :=
    Computable.option_casesOn (hr₂.comp Computable.fst) (Computable.const false) hbody
  refine (Computable.option_casesOn hr₁ (Computable.const false) hinner).of_eq fun t ↦ ?_
  dsimp only
  cases h₁ : OscNode.rawNode f P t.2.1.1 <;> cases h₂ : OscNode.rawNode f P t.2.2.1 <;>
    simp only [oscBracketOk, h₁, h₂]

attribute [local irreducible] oscBracketOk

/-! ### Soundness -/

/-- The real content of a passed certificate. -/
theorem oscBracketOk_sound {q j : ℕ} {b : OscBracket} (hb : oscBracketOk f P q j b = true) :
    ∃ (e₁ e₂ : Endpoint f P), e₁.path = b.1.1 ∧ e₁.right = b.1.2 ∧
      e₁.coord ≤ ((NNRatCode.value (RatCode.clampUnit q) : ℚ) : ℝ) ∧
      ((NNRatCode.value (RatCode.clampUnit q) : ℚ) : ℝ) ≤ e₂.coord ∧
      |((NNRatCode.value (OscNode.sideValueCode f e₂.node e₂.right j) : ℚ) : ℝ)
        - ((NNRatCode.value (OscNode.sideValueCode f e₁.node e₁.right j) : ℚ) : ℝ)|
        ≤ 3 * (2⁻¹ : ℝ) ^ j := by
  unfold oscBracketOk at hb
  cases h₁ : OscNode.rawNode f P b.1.1 with
  | none =>
    rw [h₁] at hb
    cases h₂ : OscNode.rawNode f P b.2.1 <;> rw [h₂] at hb <;> exact absurd hb (by simp)
  | some n₁ =>
  cases h₂ : OscNode.rawNode f P b.2.1 with
  | none => rw [h₁, h₂] at hb; exact absurd hb (by simp)
  | some n₂ =>
  rw [h₁, h₂] at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hle₁, hle₂⟩, hgap₁⟩, hgap₂⟩ := hb
  rw [RatCode.le_iff, RatCode.value_ofNNRat] at hle₁ hle₂
  rw [NNRatCode.le_iff, NNRatCode.value_sub, tsub_le_iff_right] at hgap₁ hgap₂
  refine ⟨⟨b.1.1, b.1.2, n₁, h₁⟩, ⟨b.2.1, b.2.2, n₂, h₂⟩, rfl, rfl, ?_, ?_, ?_⟩
  · rw [Endpoint.coord, ← OscNode.value_sideCode]
    exact_mod_cast hle₁
  · rw [Endpoint.coord, ← OscNode.value_sideCode]
    exact_mod_cast hle₂
  · rw [abs_le]
    have g₁ : ((NNRatCode.value (OscNode.sideValueCode f n₂ b.2.2 j) : ℚ) : ℝ)
        ≤ ((NNRatCode.value (oscGapCode j) : ℚ) : ℝ)
          + ((NNRatCode.value (OscNode.sideValueCode f n₁ b.1.2 j) : ℚ) : ℝ) := by
      exact_mod_cast hgap₁
    have g₂ : ((NNRatCode.value (OscNode.sideValueCode f n₁ b.1.2 j) : ℚ) : ℝ)
        ≤ ((NNRatCode.value (oscGapCode j) : ℚ) : ℝ)
          + ((NNRatCode.value (OscNode.sideValueCode f n₂ b.2.2 j) : ℚ) : ℝ) := by
      exact_mod_cast hgap₂
    rw [value_oscGapCode] at g₁ g₂
    constructor <;> linarith

/-- The first coded value of a passed certificate approximates the function at the clamped
argument to within `4 · 2⁻ʲ`. -/
theorem oscBracketOk_approx {q j : ℕ} {b : OscBracket} (hb : oscBracketOk f P q j b = true)
    {n₁ : OscNode} (h₁ : OscNode.rawNode f P b.1.1 = some n₁) :
    |((NNRatCode.value (OscNode.sideValueCode f n₁ b.1.2 j) : ℚ) : ℝ)
        - oscFun f P ((NNRatCode.value (RatCode.clampUnit q) : ℚ) : ℝ)| ≤ 4 * (2⁻¹ : ℝ) ^ j := by
  obtain ⟨e₁, e₂, hp, hs, hc₁, hc₂, hgap⟩ := oscBracketOk_sound f P hb
  have hn : e₁.node = n₁ := by
    have := e₁.node_eq
    rw [hp, h₁] at this
    exact (Option.some.inj this).symm
  have hv₁ := OscNode.sideValueCode_error f e₁.node e₁.right j
  have hv₂ := OscNode.sideValueCode_error f e₂.node e₂.right j
  have hlo := e₁.value_le_oscFun f P hc₁
  have hhi := oscFun.le_of_le_coord f P e₂ hc₂
  rw [← hn, ← hs]
  rw [abs_le] at hv₁ hv₂ hgap ⊢
  simp only [Endpoint.value] at hlo hhi
  constructor <;> linarith

/-! ### Existence -/

/-- Around every point of the unit interval there are named endpoints with values as close as
desired. -/
theorem exists_endpoint_bracket {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) :
    ∃ e₁ e₂ : Endpoint f P, e₁.coord ≤ r ∧ r ≤ e₂.coord ∧ e₂.value - e₁.value ≤ η := by
  have hcont := oscFun_continuousOn f P r hr
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδH⟩ := hcont (η / 2) (by linarith)
  -- a name at or below `r`, within `δ`
  have hleft : ∃ e₁ : Endpoint f P, e₁.coord ≤ r ∧ oscFun f P r - η / 2 ≤ e₁.value := by
    rcases eq_or_lt_of_le hr.1 with h0 | h0
    · refine ⟨Endpoint.rootLeft, by simp [← h0], ?_⟩
      rw [← h0, oscFun.zero, Endpoint.value_rootLeft]
      linarith
    · obtain ⟨e, he⟩ := exists_endpoint_mem_Ioo f P (a := max 0 (r - δ)) (b := r)
        (max_lt h0 (by linarith)) (le_max_left _ _) hr.2
      rw [Set.mem_Ioo, max_lt_iff] at he
      refine ⟨e, he.2.le, ?_⟩
      have hd := hδH (show e.coord ∈ Set.Icc (0 : ℝ) 1 from e.coord_mem_unit)
        (show dist e.coord r < δ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt, oscFun.endpoint] at hd
      linarith
  have hright : ∃ e₂ : Endpoint f P, r ≤ e₂.coord ∧ e₂.value ≤ oscFun f P r + η / 2 := by
    rcases eq_or_lt_of_le hr.2 with h1 | h1
    · refine ⟨Endpoint.rootRight, by simp [h1], ?_⟩
      rw [h1, oscFun.one, Endpoint.value_rootRight]
      linarith
    · obtain ⟨e, he⟩ := exists_endpoint_mem_Ioo f P (a := r) (b := min 1 (r + δ))
        (lt_min h1 (by linarith)) hr.1 (min_le_left _ _)
      rw [Set.mem_Ioo, lt_min_iff] at he
      refine ⟨e, he.1.le, ?_⟩
      have hd := hδH (show e.coord ∈ Set.Icc (0 : ℝ) 1 from e.coord_mem_unit)
        (show dist e.coord r < δ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt, oscFun.endpoint] at hd
      linarith
  obtain ⟨e₁, h₁, hv₁⟩ := hleft
  obtain ⟨e₂, h₂, hv₂⟩ := hright
  exact ⟨e₁, e₂, h₁, h₂, by linarith⟩

theorem exists_oscBracketOk (q j : ℕ) : ∃ b : OscBracket, oscBracketOk f P q j b = true := by
  set r : ℝ := ((NNRatCode.value (RatCode.clampUnit q) : ℚ) : ℝ) with hr
  have hr01 : r ∈ Set.Icc (0 : ℝ) 1 := by
    have h := RatCode.value_clampUnit q
    have h1 : ((NNRatCode.value (RatCode.clampUnit q) : ℚ≥0) : ℚ) ≤ 1 := by
      rw [h]; exact max_le zero_le_one (min_le_left _ _)
    refine ⟨by positivity, ?_⟩
    rw [hr]
    exact_mod_cast h1
  obtain ⟨e₁, e₂, hc₁, hc₂, hgap⟩ := exists_endpoint_bracket f P hr01 (η := (2⁻¹ : ℝ) ^ j)
    (by positivity)
  refine ⟨((e₁.path, e₁.right), (e₂.path, e₂.right)), ?_⟩
  unfold oscBracketOk
  simp only [e₁.node_eq, e₂.node_eq, Bool.and_eq_true]
  have hv₁ := OscNode.sideValueCode_error f e₁.node e₁.right j
  have hv₂ := OscNode.sideValueCode_error f e₂.node e₂.right j
  rw [abs_le] at hv₁ hv₂
  have hord : e₁.value ≤ e₂.value := e₁.value_mono e₂ (le_trans hc₁ hc₂)
  simp only [Endpoint.value] at hv₁ hv₂ hord hgap
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [RatCode.le_iff, RatCode.value_ofNNRat]
    have : ((RatCode.value (OscNode.sideCode e₁.node e₁.right) : ℚ) : ℝ) ≤ r := by
      rw [OscNode.value_sideCode]; exact hc₁
    rw [hr] at this
    exact_mod_cast this
  · rw [RatCode.le_iff, RatCode.value_ofNNRat]
    have : r ≤ ((RatCode.value (OscNode.sideCode e₂.node e₂.right) : ℚ) : ℝ) := by
      rw [OscNode.value_sideCode]; exact hc₂
    rw [hr] at this
    exact_mod_cast this
  · rw [NNRatCode.le_iff, NNRatCode.value_sub, tsub_le_iff_right]
    have : ((NNRatCode.value (OscNode.sideValueCode f e₂.node e₂.right j) : ℚ) : ℝ)
        ≤ ((NNRatCode.value (oscGapCode j) : ℚ) : ℝ)
          + ((NNRatCode.value (OscNode.sideValueCode f e₁.node e₁.right j) : ℚ) : ℝ) := by
      rw [value_oscGapCode]; linarith
    exact_mod_cast this
  · rw [NNRatCode.le_iff, NNRatCode.value_sub, tsub_le_iff_right]
    have : ((NNRatCode.value (OscNode.sideValueCode f e₁.node e₁.right j) : ℚ) : ℝ)
        ≤ ((NNRatCode.value (oscGapCode j) : ℚ) : ℝ)
          + ((NNRatCode.value (OscNode.sideValueCode f e₂.node e₂.right j) : ℚ) : ℝ) := by
      rw [value_oscGapCode]; linarith
    exact_mod_cast this

/-! ### The search -/

/-- Decoding of candidates through the primitive-recursive coding, pinned so that the instance is
the one `Computable.decode` speaks about. -/
def decodeBracket (t : ℕ) : Option OscBracket :=
  @Encodable.decode OscBracket Primcodable.toEncodable t

theorem computable_decodeBracket : Computable decodeBracket := Computable.decode

theorem decodeBracket_encode (b : OscBracket) :
    decodeBracket (@Encodable.encode OscBracket Primcodable.toEncodable b) = some b :=
  Encodable.encodek b

/-- The test on an encoded candidate. -/
noncomputable def oscBracketTest (q j t : ℕ) : Bool :=
  match decodeBracket t with
  | some b => oscBracketOk f P q j b
  | none => false

theorem computable_oscBracketTest :
    Computable fun w : (ℕ × ℕ) × ℕ ↦ oscBracketTest f P w.1.1 w.1.2 w.2 := by
  have hdec : Computable fun w : (ℕ × ℕ) × ℕ ↦ decodeBracket w.2 :=
    computable_decodeBracket.comp Computable.snd
  have hok : Computable fun p : ((ℕ × ℕ) × ℕ) × OscBracket ↦ oscBracketOk f P p.1.1.1 p.1.1.2 p.2 :=
    Computable.comp (f := fun t : (ℕ × ℕ) × OscBracket ↦ oscBracketOk f P t.1.1 t.1.2 t.2)
      (g := fun p : ((ℕ × ℕ) × ℕ) × OscBracket ↦ (p.1.1, p.2)) (computable_oscBracketOk f P)
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  refine (Computable.option_casesOn
    (g := fun (w : (ℕ × ℕ) × ℕ) (b : OscBracket) ↦ oscBracketOk f P w.1.1 w.1.2 b)
    hdec (Computable.const false) hok).of_eq fun w ↦ ?_
  dsimp only
  cases h : decodeBracket w.2 <;> simp only [oscBracketTest, h]

attribute [local irreducible] oscBracketTest

theorem exists_oscBracketTest (q j : ℕ) : ∃ t, oscBracketTest f P q j t = true := by
  obtain ⟨b, hb⟩ := exists_oscBracketOk f P q j
  refine ⟨@Encodable.encode OscBracket Primcodable.toEncodable b, ?_⟩
  simp only [oscBracketTest, decodeBracket_encode]
  exact hb

/-- The search on paired input `⟨q, k⟩`, at precision `k + 3`. -/
noncomputable def oscBracketSearch (w : ℕ) : Part ℕ :=
  Nat.rfind fun t ↦ Part.some (oscBracketTest f P w.unpair.1 (w.unpair.2 + 3) t)

theorem partrec_oscBracketSearch : Nat.Partrec (oscBracketSearch f P) := by
  have hin : Computable fun p : ℕ × ℕ ↦ ((p.1.unpair.1, p.1.unpair.2 + 3), p.2) :=
    ((Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).pair
      ((Primrec.nat_add.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
        (Primrec.const 3)))).to_comp.pair Computable.snd
  have h : Computable fun p : ℕ × ℕ ↦ oscBracketTest f P p.1.unpair.1 (p.1.unpair.2 + 3) p.2 :=
    ((computable_oscBracketTest f P).comp hin).of_eq fun _ ↦ rfl
  exact Partrec.nat_iff.mp (Partrec.rfind (Computable₂.partrec₂ h.to₂))

theorem oscBracketSearch_dom (w : ℕ) : (oscBracketSearch f P w).Dom := by
  obtain ⟨t, ht⟩ := exists_oscBracketTest f P w.unpair.1 (w.unpair.2 + 3)
  obtain ⟨m, hm, -⟩ := Nat.rfind_min'
    (p := fun t ↦ oscBracketTest f P w.unpair.1 (w.unpair.2 + 3) t) ht
  exact Part.dom_iff_mem.mpr ⟨m, hm⟩

/-- The bundled search. -/
noncomputable def oscBracketIndexCode : NatFunctionCode :=
  NatFunctionCode.ofPartrecTotal (partrec_oscBracketSearch f P) (oscBracketSearch_dom f P)

/-- The index of the selected certificate. -/
noncomputable def oscBracketIndex (w : ℕ) : ℕ := (oscBracketIndexCode f P).toFun w

theorem computable_oscBracketIndex : Computable (oscBracketIndex f P) :=
  (oscBracketIndexCode f P).computable_toFun

theorem oscBracketTest_oscBracketIndex (w : ℕ) :
    oscBracketTest f P w.unpair.1 (w.unpair.2 + 3) (oscBracketIndex f P w) = true := by
  have hmem : oscBracketIndex f P w ∈ oscBracketSearch f P w := by
    rw [oscBracketIndex, oscBracketIndexCode, NatFunctionCode.ofPartrecTotal_toFun]
    exact Part.get_mem _
  simpa using Nat.rfind_spec hmem

/-- The first coded value of an encoded candidate, as a signed code. -/
noncomputable def oscBracketOutput (j t : ℕ) : ℕ :=
  match decodeBracket t with
  | some b =>
    match OscNode.rawNode f P b.1.1 with
    | some n₁ => RatCode.ofNNRat (OscNode.sideValueCode f n₁ b.1.2 j)
    | none => RatCode.ofNat 0
  | none => RatCode.ofNat 0

theorem computable_oscBracketOutput :
    Computable fun w : ℕ × ℕ ↦ oscBracketOutput f P w.1 w.2 := by
  have hdec : Computable fun w : ℕ × ℕ ↦ decodeBracket w.2 :=
    computable_decodeBracket.comp Computable.snd
  have hr : Computable fun p : (ℕ × ℕ) × OscBracket ↦ OscNode.rawNode f P p.2.1.1 :=
    Computable.comp (f := OscNode.rawNode f P) (g := fun p : (ℕ × ℕ) × OscBracket ↦ p.2.1.1)
      (OscNode.computable_rawNode f P) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).to_comp
  have hsv : Computable fun p : ((ℕ × ℕ) × OscBracket) × OscNode ↦
      OscNode.sideValueCode f p.2 p.1.2.1.2 p.1.1.1 :=
    Computable.comp (f := fun q : OscNode × Bool × ℕ ↦ OscNode.sideValueCode f q.1 q.2.1 q.2.2)
      (g := fun p : ((ℕ × ℕ) × OscBracket) × OscNode ↦ (p.2, p.1.2.1.2, p.1.1.1))
      (OscNode.computable_sideValueCode f)
      (Computable.snd.pair ((Primrec.snd.comp (Primrec.fst.comp
        (Primrec.snd.comp Primrec.fst))).to_comp.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).to_comp))
  have hinner : Computable fun p : (ℕ × ℕ) × OscBracket ↦
      Option.casesOn (motive := fun _ ↦ ℕ) (OscNode.rawNode f P p.2.1.1) (RatCode.ofNat 0)
        (fun n₁ ↦ RatCode.ofNNRat (OscNode.sideValueCode f n₁ p.2.1.2 p.1.1)) :=
    Computable.option_casesOn
      (g := fun (p : (ℕ × ℕ) × OscBracket) (n₁ : OscNode) ↦
        RatCode.ofNNRat (OscNode.sideValueCode f n₁ p.2.1.2 p.1.1))
      hr (Computable.const _) (RatCode.primrec_ofNNRat.to_comp.comp hsv)
  refine (Computable.option_casesOn
    (g := fun (w : ℕ × ℕ) (b : OscBracket) ↦
      Option.casesOn (motive := fun _ ↦ ℕ) (OscNode.rawNode f P b.1.1) (RatCode.ofNat 0)
        (fun n₁ ↦ RatCode.ofNNRat (OscNode.sideValueCode f n₁ b.1.2 w.1)))
    hdec (Computable.const (RatCode.ofNat 0)) hinner).of_eq fun w ↦ ?_
  dsimp only
  cases h : decodeBracket w.2 with
  | none => simp only [oscBracketOutput, h]
  | some b =>
    simp only [oscBracketOutput, h]
    cases OscNode.rawNode f P b.1.1 <;> rfl

attribute [local irreducible] oscBracketOutput

/-- The approximation program on `⟨q, k⟩`. -/
noncomputable def oscApproxFun (w : ℕ) : ℕ :=
  oscBracketOutput f P (w.unpair.2 + 3) (oscBracketIndex f P w)

theorem computable_oscApproxFun : Computable (oscApproxFun f P) :=
  Computable.comp (f := fun w : ℕ × ℕ ↦ oscBracketOutput f P w.1 w.2)
    (g := fun w : ℕ ↦ (w.unpair.2 + 3, oscBracketIndex f P w)) (computable_oscBracketOutput f P)
    ((Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 3)).to_comp.pair
      (computable_oscBracketIndex f P))

theorem oscApproxFun_spec (q k : ℕ) :
    |oscFun f P ((NNRatCode.value (RatCode.clampUnit q) : ℚ) : ℝ)
        - ((RatCode.value (oscApproxFun f P (Nat.pair q k)) : ℚ) : ℝ)| ≤ (2⁻¹ : ℝ) ^ k := by
  have ht := oscBracketTest_oscBracketIndex f P (Nat.pair q k)
  rw [Nat.unpair_pair] at ht
  simp only [oscApproxFun, Nat.unpair_pair]
  unfold oscBracketTest at ht
  unfold oscBracketOutput
  cases hd : decodeBracket (oscBracketIndex f P (Nat.pair q k)) with
  | none => rw [hd] at ht; exact absurd ht (by simp)
  | some b =>
  rw [hd] at ht
  simp only at ht
  obtain ⟨e₁, -, hp, -, -, -, -⟩ := oscBracketOk_sound f P ht
  have h₁ : OscNode.rawNode f P b.1.1 = some e₁.node := by rw [← hp]; exact e₁.node_eq
  simp only [h₁]
  have happrox := oscBracketOk_approx f P ht h₁
  rw [RatCode.value_ofNNRat, abs_sub_comm]
  refine le_trans happrox ?_
  rw [pow_add]
  have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) k
  norm_num
  linarith

/-! ## Packaging -/

/-- The values on nonnegative rationals. -/
noncomputable def oscValues (q : ℚ≥0) : ℝ := oscFun f P ((q : ℚ) : ℝ)

theorem oscValues_monotone : Monotone (oscValues f P) := fun p q h ↦
  oscFun.monotone f P (by exact_mod_cast h)

/-- The extension of the rational values recovers the function on the unit interval. -/
theorem supExtend_oscValues (x : Set.Icc (0 : ℝ) 1) :
    supExtend (oscValues f P) x = oscFun f P x := by
  rw [supExtend]
  haveI := nonempty_supExtend_index x
  refine le_antisymm (ciSup_le fun q ↦ oscFun.monotone f P q.2) ?_
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  -- left-continuity within the unit interval supplies a rational below `x` with a close value
  have hcont := oscFun_continuousOn f P x x.2
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδH⟩ := hcont η hη
  obtain ⟨q, hqx, hqδ⟩ : ∃ q : ℚ≥0, ((q : ℚ) : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) - ((q : ℚ) : ℝ) < δ := by
    rcases eq_or_lt_of_le x.2.1 with h0 | h0
    · exact ⟨0, by rw [← h0]; simp, by rw [← h0]; simpa using hδ⟩
    · obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show max 0 ((x : ℝ) - δ) < (x : ℝ) from
        max_lt h0 (by linarith))
      rw [max_lt_iff] at hr₁
      exact ⟨⟨r, by exact_mod_cast hr₁.1.le⟩, hr₂.le, by simp only [NNRat.coe_mk]; linarith⟩
  have hd := hδH (show ((q : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨by positivity, by linarith [x.2.2]⟩)
    (show dist ((q : ℚ) : ℝ) (x : ℝ) < δ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at hd
  have hle := le_ciSup (bddAbove_supExtend_index (oscValues_monotone f P) x) ⟨q, hqx⟩
  simp only [oscValues] at hle ⊢
  linarith

/-- **The oscillating function**, bundled: continuous and nondecreasing on the unit interval, with
the bracket-search program as its approximation. -/
noncomputable def oscMonotone : ComputableMonotone :=
  ofRationalValues (oscValues f P) (oscValues_monotone f P)
    (by
      have h : supExtend (oscValues f P) = fun x : Set.Icc (0 : ℝ) 1 ↦ oscFun f P x :=
        funext (supExtend_oscValues f P)
      rw [h]
      exact continuousOn_iff_continuous_restrict.mp (oscFun_continuousOn f P))
    (NatFunctionCode.ofComputable (computable_oscApproxFun f P))
    (fun q k ↦ by
      rw [NatFunctionCode.apply₂, NatFunctionCode.ofComputable_toFun]
      exact oscApproxFun_spec f P q k)

theorem oscMonotone_unitFun (x : Set.Icc (0 : ℝ) 1) :
    (oscMonotone f P).unitFun x = oscFun f P x :=
  supExtend_oscValues f P x

end AlgorithmicRandomness
