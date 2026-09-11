/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.OscillationTree

/-!
# The node invariant and path mass convergence

The raw nodes of `OscillationTree` are arbitrary syntax. This file states what the generated ones
satisfy — a connected history from the unit interval, exact cell representation, and the phase
equation against the anchor — proves that every successful step preserves it, and derives the
edge bounds that make width and mass vanish along every infinite path (BMN Claim 4.4).

The phase clause preserves the endpoint *values*, not merely the mass ratio: the current frame's
endpoint values are the interpolation from the anchor's values. A mass ratio alone would leave the
vertical offset unspecified, which the later endpoint-consistency argument needs. The two mass
identities follow from it.

Nothing here takes a point or an oscillation witness. The slope certificate on a betting parent is
supplied by the next successful edge: continuing into betting means the sample on the parent was
resolved to betting, and the sampler's error bound turns that into `slope ≤ γ + margin`.
-/

open Filter Topology

open scoped NNRat

namespace AlgorithmicRandomness

/-! ## Connected histories -/

/-- `e` leads from the unit interval to `I`: each instruction's parent is the preceding interval,
each instruction is valid, and each target is nondegenerate. Individual validity does not connect
the instructions; this does. -/
inductive OscValueExpr.Connected : OscValueExpr → RatIntervalCode → Prop
  | nil : Connected [] RatIntervalCode.unit
  | snoc {e : OscValueExpr} {I : RatIntervalCode} (h : Connected e I) (b : Bool)
      {J : RatIntervalCode} (hv : (⟨b, I, J⟩ : OscInterpStep).valid = true) (hw : 0 < J.width) :
      Connected (e ++ [⟨b, I, J⟩]) J

namespace OscValueExpr.Connected

theorem width_pos {e : OscValueExpr} {I : RatIntervalCode} (h : Connected e I) : 0 < I.width := by
  cases h with
  | nil => simp
  | snoc _ _ _ hw => exact hw

theorem left_nonneg {e : OscValueExpr} {I : RatIntervalCode} (h : Connected e I) : 0 ≤ I.left := by
  induction h with
  | nil => simp
  | snoc _ _ hv _ =>
    obtain ⟨-, h0, -, hl, -⟩ := (OscInterpStep.valid_iff _).mp hv
    exact le_trans h0 hl

theorem right_le_one {e : OscValueExpr} {I : RatIntervalCode} (h : Connected e I) :
    I.right ≤ 1 := by
  induction h with
  | nil => simp [RatIntervalCode.right]
  | snoc _ _ hv _ =>
    obtain ⟨-, -, h1, -, hr⟩ := (OscInterpStep.valid_iff _).mp hv
    exact le_trans hr h1

/-- The two shapes a connected history can take, with the indices free so that `cases` applies. -/
theorem cases_eq {l : OscValueExpr} {J : RatIntervalCode} (h : Connected l J) :
    (l = [] ∧ J = RatIntervalCode.unit) ∨
      ∃ (e : OscValueExpr) (b : Bool) (I : RatIntervalCode), l = e ++ [⟨b, I, J⟩] ∧
        Connected e I ∧ (⟨b, I, J⟩ : OscInterpStep).valid = true ∧ 0 < J.width := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | snoc h' b hv hw => exact Or.inr ⟨_, b, _, rfl, h', hv, hw⟩

theorem of_nil {J : RatIntervalCode} (h : Connected [] J) : J = RatIntervalCode.unit := by
  rcases cases_eq h with ⟨-, rfl⟩ | ⟨e, b, I, he, -⟩
  · rfl
  · exact absurd he.symm (List.append_ne_nil_of_right_ne_nil e (by simp))

/-- Inversion of a nonempty connected history. -/
theorem of_append_singleton {e : OscValueExpr} {s : OscInterpStep} {J : RatIntervalCode}
    (h : Connected (e ++ [s]) J) :
    Connected e s.parent ∧ s.target = J ∧ s.valid = true ∧ 0 < J.width := by
  rcases cases_eq h with ⟨he, -⟩ | ⟨e', b, I, he, h', hv, hw⟩
  · exact absurd he (List.append_ne_nil_of_right_ne_nil e (by simp))
  · obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp he
    exact ⟨h', rfl, hv, hw⟩

theorem interval_eq {e : OscValueExpr} {I J : RatIntervalCode} (hI : Connected e I)
    (hJ : Connected e J) : I = J := by
  induction e using List.reverseRecOn with
  | nil => rw [of_nil hI, of_nil hJ]
  | append_singleton e s _ =>
    obtain ⟨-, h1, -, -⟩ := of_append_singleton hI
    obtain ⟨-, h2, -, -⟩ := of_append_singleton hJ
    rw [← h1, ← h2]

/-- The interval of a longer connected history sits inside that of a prefix. -/
theorem interval_subset_of_prefix {e e' : OscValueExpr} {I J : RatIntervalCode}
    (hI : Connected e I) (hJ : Connected e' J) (hpre : e <+: e') : J.interval ⊆ I.interval := by
  induction hJ generalizing I with
  | nil =>
    rw [List.prefix_nil] at hpre
    subst hpre
    rw [of_nil hI]
  | @snoc e' I' h' b J' hv hw ih =>
    rcases List.prefix_concat_iff.mp hpre with rfl | hpre'
    · rw [interval_eq hI (Connected.snoc h' b hv hw)]
    · refine Set.Subset.trans ?_ (ih hI hpre')
      obtain ⟨-, -, -, hl, hr⟩ := (OscInterpStep.valid_iff _).mp hv
      exact Set.Icc_subset_Icc hl hr

end OscValueExpr.Connected

/-! ## Interpolation composition

Interpolating through a nested intermediate interval, in the same mode, equals interpolating
directly from the outer one. -/

section Composition

variable (f : ComputableMonotone)

theorem interpWeight_comp (b : Bool) {A B : RatIntervalCode} (hA : 0 < A.width)
    (hA0 : 0 ≤ A.left) (hA1 : A.right ≤ 1) (hB : 0 < B.width)
    (hBA : B.interval ⊆ A.interval) (t : ℝ) :
    interpWeight f b A B.left
        + (interpWeight f b A B.right - interpWeight f b A B.left) * interpWeight f b B t
      = interpWeight f b A t := by
  have hBl : B.left ∈ A.interval := hBA (Set.left_mem_Icc.mpr (by
    rw [RatIntervalCode.right]; linarith [B.width_nonneg]))
  have hBr : B.right ∈ A.interval := hBA (Set.right_mem_Icc.mpr (by
    rw [RatIntervalCode.right]; linarith [B.width_nonneg]))
  have hB0 : 0 ≤ B.left := le_trans hA0 hBl.1
  have hB1 : B.right ≤ 1 := le_trans hBr.2 hA1
  cases b
  · simp only [interpWeight, Bool.false_eq_true, if_false]
    have hw : B.right = B.left + B.width := by rw [RatIntervalCode.right]
    field_simp
    rw [hw]
    ring
  · simp only [interpWeight, if_true]
    have hgapA := width_le_addIdentity_gap f hA0 hA1
    have hgapB := width_le_addIdentity_gap f hB0 hB1
    have hDA : f.addIdentity.toFun A.right - f.addIdentity.toFun A.left ≠ 0 := by linarith
    have hDB : f.addIdentity.toFun B.right - f.addIdentity.toFun B.left ≠ 0 := by linarith
    field_simp
    ring

theorem interp_comp (b : Bool) {A B : RatIntervalCode} (hA : 0 < A.width) (hA0 : 0 ≤ A.left)
    (hA1 : A.right ≤ 1) (hB : 0 < B.width) (hBA : B.interval ⊆ A.interval) (L R t : ℝ) :
    interp f b B (interp f b A L R B.left) (interp f b A L R B.right) t = interp f b A L R t := by
  simp only [interp]
  rw [← interpWeight_comp f b hA hA0 hA1 hB hBA t]
  ring

end Composition

/-! ## Strict positivity of the mass along connected histories -/

section Strict

variable (f : ComputableMonotone)

theorem interpWeight_lt (b : Bool) {A : RatIntervalCode} (hw : 0 < A.width) (h0 : 0 ≤ A.left)
    (h1 : A.right ≤ 1) {s t : ℝ} (hs : s ∈ A.interval) (ht : t ∈ A.interval) (hst : s < t) :
    interpWeight f b A s < interpWeight f b A t := by
  cases b
  · simp only [interpWeight, Bool.false_eq_true, if_false]
    exact div_lt_div_of_pos_right (by linarith) hw
  · simp only [interpWeight, if_true]
    have hgap := width_le_addIdentity_gap f h0 h1
    have hF := f.sub_le_addIdentity_sub ⟨le_trans h0 hs.1, le_trans hs.2 h1⟩
      ⟨le_trans h0 ht.1, le_trans ht.2 h1⟩ hst.le
    exact div_lt_div_of_pos_right (by linarith) (by linarith)

theorem OscValueExpr.Connected.eval_lt {e : OscValueExpr} {I : RatIntervalCode}
    (h : OscValueExpr.Connected e I) : (OscValueExpr.eval f e).1 < (OscValueExpr.eval f e).2 := by
  induction h with
  | nil => simp
  | @snoc e I h' b J hv hw ih =>
    rw [OscValueExpr.eval_append_singleton, OscInterpStep.apply_of_valid f hv]
    obtain ⟨hIw, h0, h1, hl, hr⟩ := (OscInterpStep.valid_iff _).mp hv
    have hJ : J.left < J.right := by rw [RatIntervalCode.right]; linarith
    have hθ := interpWeight_lt f b hIw h0 h1 (s := J.left) (t := J.right)
      ⟨hl, by linarith⟩ ⟨by linarith, hr⟩ hJ
    simp only [interp]
    nlinarith

end Strict

/-! ## Frames and the invariant -/

namespace OscFrame

variable (f : ComputableMonotone)

/-- The evaluated endpoint values of a frame. -/
noncomputable def eval (F : OscFrame) : ℝ × ℝ := OscValueExpr.eval f F.values

/-- The mass of a frame: the difference of its endpoint values. -/
noncomputable def mass (F : OscFrame) : ℝ := (F.eval f).2 - (F.eval f).1

@[simp] theorem eval_root : OscFrame.root.eval f = (0, 1) := rfl

end OscFrame

namespace OscNode

/-- The grid a state uses. -/
def gridOf (P : OscillationParams) (betting : Bool) : AffineDyadicGrid :=
  bif betting then P.betGrid else P.waitGrid

variable (f : ComputableMonotone) (P : OscillationParams)

/-- The invariant of generated nodes. -/
structure Inv (n : OscNode) : Prop where
  /-- The history is connected from the unit interval to the node's interval. -/
  connected : n.values.Connected n.interval
  /-- Only the root has no cell. -/
  cell_none : n.cell = none → n = root
  /-- A cell is represented exactly, in the grid of the current state. -/
  cell_some : ∀ c, n.cell = some c → n.interval = (gridOf P n.betting).cellCode c
  /-- The anchor's history is connected. -/
  anchor_connected : n.phaseStart.values.Connected n.phaseStart.interval
  /-- The anchor's history is a prefix of the current one. -/
  anchor_prefix : n.phaseStart.values <+: n.values
  /-- The left value is the interpolation from the anchor's values, in the current mode. -/
  phase_left : (n.toOscFrame.eval f).1 = interp f n.betting n.phaseStart.interval
    (n.phaseStart.eval f).1 (n.phaseStart.eval f).2 n.interval.left
  /-- The right value likewise. -/
  phase_right : (n.toOscFrame.eval f).2 = interp f n.betting n.phaseStart.interval
    (n.phaseStart.eval f).1 (n.phaseStart.eval f).2 n.interval.right

theorem Inv.root : Inv f P root := by
  refine ⟨OscValueExpr.Connected.nil, fun _ ↦ rfl, fun c h ↦ ?_,
    OscValueExpr.Connected.nil, List.prefix_rfl, ?_, ?_⟩
  · change (none : Option AffineDyadicCell) = some c at h
    cases h
  · change (0 : ℝ) = interp f true RatIntervalCode.unit 0 1 RatIntervalCode.unit.left
    rw [interp_left]
  · change (1 : ℝ) = interp f true RatIntervalCode.unit 0 1 RatIntervalCode.unit.right
    rw [interp_right f true (by simp) (by simp) (by simp [RatIntervalCode.right])]

/-- Derived containment: the node's interval sits inside the anchor's. -/
theorem Inv.interval_subset_anchor {n : OscNode} (h : Inv f P n) :
    n.interval.interval ⊆ n.phaseStart.interval.interval :=
  OscValueExpr.Connected.interval_subset_of_prefix h.anchor_connected h.connected h.anchor_prefix

theorem Inv.mass_pos {n : OscNode} (h : Inv f P n) : 0 < n.toOscFrame.mass f := by
  have := h.connected.eval_lt f
  rw [OscFrame.mass]
  exact sub_pos.mpr this

theorem Inv.mass_eq {n : OscNode} (h : Inv f P n) :
    n.toOscFrame.mass f = ((n.phaseStart.eval f).2 - (n.phaseStart.eval f).1)
      * (interpWeight f n.betting n.phaseStart.interval n.interval.right
        - interpWeight f n.betting n.phaseStart.interval n.interval.left) := by
  rw [OscFrame.mass, h.phase_left, h.phase_right, interp_sub_interp]

/-- The betting mass identity: `g[B] / F[B] = g[A] / F[A]`, cross-multiplied. -/
theorem Inv.mass_betting {n : OscNode} (h : Inv f P n) (hb : n.betting = true) :
    n.toOscFrame.mass f
        * (f.addIdentity.toFun n.phaseStart.interval.right
          - f.addIdentity.toFun n.phaseStart.interval.left)
      = n.phaseStart.mass f
        * (f.addIdentity.toFun n.interval.right - f.addIdentity.toFun n.interval.left) := by
  have hA := h.anchor_connected
  rw [OscFrame.mass, h.phase_left, h.phase_right, hb, OscFrame.mass]
  exact mass_betting_step f hA.width_pos hA.left_nonneg hA.right_le_one _ _ _ _

/-- The waiting mass identity: `g[B] / |B| = g[A] / |A|`, cross-multiplied. -/
theorem Inv.mass_waiting {n : OscNode} (h : Inv f P n) (hb : n.betting = false) :
    n.toOscFrame.mass f * n.phaseStart.interval.width
      = n.phaseStart.mass f * n.interval.width := by
  have hA := h.anchor_connected
  rw [OscFrame.mass, h.phase_left, h.phase_right, hb, OscFrame.mass]
  have := mass_waiting_step f hA.width_pos ((n.phaseStart.eval f).1) ((n.phaseStart.eval f).2)
    n.interval.left n.interval.right
  rw [this, RatIntervalCode.right]
  ring

/-! ## Edges -/

/-- A successful step from `n` to `n'`. -/
def Step (n n' : OscNode) : Prop := ∃ m, step f P n m = some n'

/-- The node a binary move produces. -/
def binaryNode (n : OscNode) (b : Bool) : OscNode :=
  { interval := n.interval.child b
    values := n.values ++ [⟨n.betting, n.interval, n.interval.child b⟩]
    betting := n.betting
    cell := n.cell.map fun c ↦ c.child b
    phaseStart := n.phaseStart }

/-- The node a regridding move produces. -/
def regridNode (G : AffineDyadicGrid) (nb : Bool) (n : OscNode) (c : AffineDyadicCell) :
    OscNode :=
  { interval := G.cellCode c
    values := n.values ++ [⟨nb, n.interval, G.cellCode c⟩]
    betting := nb
    cell := some c
    phaseStart := bif switched nb n then n.toOscFrame else n.phaseStart }

theorem binaryStep_eq (nb : Bool) (n : OscNode) (b : Bool) :
    binaryStep nb n b = bif needsRegrid nb n then none else some (binaryNode n b) := rfl

theorem regridStep_eq (G : AffineDyadicGrid) (nb : Bool) (n : OscNode) (c : AffineDyadicCell) :
    regridStep G nb n c =
      bif needsRegrid nb n && regridChild n.interval G (!nb) c then some (regridNode G nb n c)
      else none := rfl

/-- The two shapes of a successful step. -/
theorem Step.elim {n n' : OscNode} (hs : Step f P n n') :
    (∃ b, needsRegrid (nextBetting f P n) n = false ∧ n' = binaryNode n b) ∨
    (∃ c, needsRegrid (nextBetting f P n) n = true ∧
      regridChild n.interval (gridOf P (nextBetting f P n)) (!nextBetting f P n) c = true ∧
      n' = regridNode (gridOf P (nextBetting f P n)) (nextBetting f P n) n c) := by
  obtain ⟨m, hm⟩ := hs
  rcases m with b | c
  · rw [step_inl, binaryStep_eq] at hm
    cases h : needsRegrid (nextBetting f P n) n
    · rw [h, cond_false] at hm
      exact Or.inl ⟨b, rfl, (Option.some.inj hm).symm⟩
    · rw [h, cond_true] at hm
      exact absurd hm (by simp)
  · rw [step_inr] at hm
    cases hnb : nextBetting f P n
    · rw [hnb, cond_false, regridStep_eq] at hm
      cases h : (needsRegrid false n && regridChild n.interval P.waitGrid (!false) c)
      · rw [h, cond_false] at hm
        exact absurd hm (by simp)
      · rw [h, cond_true] at hm
        rw [Bool.and_eq_true] at h
        exact Or.inr ⟨c, h.1, h.2, (Option.some.inj hm).symm⟩
    · rw [hnb, cond_true, regridStep_eq] at hm
      cases h : (needsRegrid true n && regridChild n.interval P.betGrid (!true) c)
      · rw [h, cond_false] at hm
        exact absurd hm (by simp)
      · rw [h, cond_true] at hm
        rw [Bool.and_eq_true] at h
        exact Or.inr ⟨c, h.1, h.2, (Option.some.inj hm).symm⟩

theorem needsRegrid_eq_false_iff (nb : Bool) (n : OscNode) :
    needsRegrid nb n = false ↔ nb = n.betting ∧ n.cell.isSome = true := by
  rw [needsRegrid, Bool.or_eq_false_iff, Bool.not_eq_false', ← Bool.not_eq_true, switched_iff]
  tauto

/-- The full state equation: a successful step ends in the resolved state. -/
theorem Step.betting_eq_nextBetting {n n' : OscNode} (hs : Step f P n n') :
    n'.betting = nextBetting f P n := by
  rcases hs.elim f P with ⟨b, hneed, rfl⟩ | ⟨c, -, -, rfl⟩
  · exact ((needsRegrid_eq_false_iff _ _).mp hneed).1.symm
  · rfl

theorem Step.cell_isSome {n n' : OscNode} (hs : Step f P n n') : n'.cell.isSome = true := by
  rcases hs.elim f P with ⟨b, hneed, rfl⟩ | ⟨c, -, -, rfl⟩
  · have := ((needsRegrid_eq_false_iff _ _).mp hneed).2
    change (n.cell.map fun c ↦ c.child b).isSome = true
    rw [Option.isSome_map]
    exact this
  · rfl

/-- Every step appends exactly one instruction, in the new state, from the old interval. -/
theorem Step.values_eq {n n' : OscNode} (hs : Step f P n n') :
    n'.values = n.values ++ [⟨n'.betting, n.interval, n'.interval⟩] := by
  rcases hs.elim f P with ⟨b, -, rfl⟩ | ⟨c, -, -, rfl⟩ <;> rfl

/-- The anchor is reset exactly on a switch. -/
theorem Step.phaseStart_eq {n n' : OscNode} (hs : Step f P n n') :
    n'.phaseStart = if n'.betting = n.betting then n.phaseStart else n.toOscFrame := by
  rcases hs.elim f P with ⟨b, hneed, rfl⟩ | ⟨c, -, -, rfl⟩
  · simp [binaryNode]
  · simp only [regridNode]
    by_cases hsw : switched (nextBetting f P n) n = true
    · rw [hsw, cond_true, if_neg ((switched_iff _ _).mp hsw)]
    · have h := (switched_iff _ _).not.mp hsw
      push Not at h
      rw [Bool.eq_false_iff.mpr hsw, cond_false, if_pos h]

theorem Step.anchor_eq_of_not_switched {n n' : OscNode} (hs : Step f P n n')
    (hb : n'.betting = n.betting) : n'.phaseStart = n.phaseStart := by
  rw [hs.phaseStart_eq f P, if_pos hb]

theorem Step.anchor_eq_of_switched {n n' : OscNode} (hs : Step f P n n')
    (hb : n'.betting ≠ n.betting) : n'.phaseStart = n.toOscFrame := by
  rw [hs.phaseStart_eq f P, if_neg hb]

theorem Step.interval_subset {n n' : OscNode} (hs : Step f P n n') :
    n'.interval.interval ⊆ n.interval.interval := by
  rcases hs.elim f P with ⟨b, -, rfl⟩ | ⟨c, -, hreg, rfl⟩
  · simp only [binaryNode]
    have hw := n.interval.width_nonneg
    rw [RatIntervalCode.interval, RatIntervalCode.interval, RatIntervalCode.right,
      RatIntervalCode.right, RatIntervalCode.left_child, RatIntervalCode.width_child]
    cases b
    · rw [if_neg (by simp)]
      exact Set.Icc_subset_Icc (by linarith) (by linarith)
    · rw [if_pos rfl]
      exact Set.Icc_subset_Icc (by linarith) (by linarith)
  · simp only [regridNode]
    rw [regridChild, Bool.and_eq_true] at hreg
    obtain ⟨⟨hl, hr⟩, -⟩ := eligible_iff.mp hreg.1
    rw [RatIntervalCode.interval, RatIntervalCode.interval, AffineDyadicGrid.left_cellCode,
      AffineDyadicGrid.right_cellCode]
    exact Set.Icc_subset_Icc hl hr

theorem Step.width_pos {n n' : OscNode} (hs : Step f P n n') (hw : 0 < n.interval.width) :
    0 < n'.interval.width := by
  rcases hs.elim f P with ⟨b, -, rfl⟩ | ⟨c, -, -, rfl⟩
  · simp only [binaryNode, RatIntervalCode.width_child]
    linarith
  · simp only [regridNode, AffineDyadicGrid.width_cellCode]
    exact AffineDyadicGrid.cellWidth_pos _ _

/-- The appended instruction of a step from an invariant node is valid. -/
theorem Step.valid {n n' : OscNode} (h : Inv f P n) (hs : Step f P n n') :
    (⟨n'.betting, n.interval, n'.interval⟩ : OscInterpStep).valid = true := by
  rw [OscInterpStep.valid_iff]
  have hsub := hs.interval_subset f P
  have hw' := hs.width_pos f P h.connected.width_pos
  have hl := hsub (Set.left_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
  have hr := hsub (Set.right_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
  exact ⟨h.connected.width_pos, h.connected.left_nonneg, h.connected.right_le_one, hl.1, hr.2⟩

theorem Step.connected {n n' : OscNode} (h : Inv f P n) (hs : Step f P n n') :
    n'.values.Connected n'.interval := by
  rw [hs.values_eq f P]
  exact OscValueExpr.Connected.snoc h.connected _ (hs.valid f P h)
    (hs.width_pos f P h.connected.width_pos)

/-- The endpoint values of the child are the interpolation from the parent's, in the new state. -/
theorem Step.eval_eq {n n' : OscNode} (h : Inv f P n) (hs : Step f P n n') :
    n'.toOscFrame.eval f = (interp f n'.betting n.interval (n.toOscFrame.eval f).1
      (n.toOscFrame.eval f).2 n'.interval.left, interp f n'.betting n.interval
        (n.toOscFrame.eval f).1 (n.toOscFrame.eval f).2 n'.interval.right) := by
  change OscValueExpr.eval f n'.values = _
  rw [hs.values_eq f P, OscValueExpr.eval_append_singleton, OscInterpStep.apply_of_valid f
    (hs.valid f P h)]
  rfl

/-- **Invariant preservation.** -/
theorem Inv.step {n n' : OscNode} (h : Inv f P n) (hs : Step f P n n') : Inv f P n' := by
  have hconn := hs.connected f P h
  have heval := hs.eval_eq f P h
  have hA := h.anchor_connected
  refine ⟨hconn, fun hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_, ?_, ?_⟩
  · have := hs.cell_isSome f P
    rw [hc] at this
    exact absurd this (by simp)
  · rcases hs.elim f P with ⟨b, hneed, rfl⟩ | ⟨c', -, -, rfl⟩
    · obtain ⟨hb, hsome⟩ := (needsRegrid_eq_false_iff _ _).mp hneed
      obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp hsome
      simp only [binaryNode, hc₀, Option.map_some] at hc ⊢
      rw [← Option.some.inj hc, AffineDyadicGrid.cellCode_child, ← h.cell_some c₀ hc₀]
    · simp only [regridNode] at hc ⊢
      rw [Option.some.inj hc]
  · rw [hs.phaseStart_eq f P]
    split_ifs
    · exact hA
    · exact h.connected
  · rw [hs.phaseStart_eq f P, hs.values_eq f P]
    split_ifs
    · exact h.anchor_prefix.trans (List.prefix_append _ _)
    · exact List.prefix_append _ _
  · rw [heval, hs.phaseStart_eq f P]
    dsimp only
    split_ifs with hb
    · rw [hb, h.phase_left, h.phase_right]
      exact (interp_comp f n.betting hA.width_pos hA.left_nonneg hA.right_le_one
        h.connected.width_pos (h.interval_subset_anchor f P) (n.phaseStart.eval f).1
        (n.phaseStart.eval f).2 n'.interval.left)
    · rfl
  · rw [heval, hs.phaseStart_eq f P]
    dsimp only
    split_ifs with hb
    · rw [hb, h.phase_left, h.phase_right]
      exact (interp_comp f n.betting hA.width_pos hA.left_nonneg hA.right_le_one
        h.connected.width_pos (h.interval_subset_anchor f P) (n.phaseStart.eval f).1
        (n.phaseStart.eval f).2 n'.interval.right)
    · rfl

end OscNode

/-! ## Edge bounds -/

theorem RatIntervalCode.width_le_of_subset {A B : RatIntervalCode}
    (h : B.interval ⊆ A.interval) : B.width ≤ A.width := by
  have hw := B.width_nonneg
  have hl := h (Set.left_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
  have hr := h (Set.right_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
  rw [RatIntervalCode.interval, Set.mem_Icc, RatIntervalCode.right] at hl hr
  rw [RatIntervalCode.right] at hr
  linarith

namespace OscNode

variable (f : ComputableMonotone) (P : OscillationParams)

theorem Step.width_le {n n' : OscNode} (hs : Step f P n n') :
    n'.interval.width ≤ n.interval.width :=
  RatIntervalCode.width_le_of_subset (hs.interval_subset f P)

/-- The child's values sit between the parent's. -/
theorem Step.eval_nested {n n' : OscNode} (h : Inv f P n) (hs : Step f P n n') :
    (n.toOscFrame.eval f).1 ≤ (n'.toOscFrame.eval f).1 ∧
      (n'.toOscFrame.eval f).1 ≤ (n'.toOscFrame.eval f).2 ∧
        (n'.toOscFrame.eval f).2 ≤ (n.toOscFrame.eval f).2 := by
  rw [hs.eval_eq f P h]
  have hc := h.connected
  have hLR := hc.eval_lt f
  have hsub := hs.interval_subset f P
  have hw' := hs.width_pos f P hc.width_pos
  have hl : n'.interval.left ∈ n.interval.interval :=
    hsub (Set.left_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
  have hr : n'.interval.right ∈ n.interval.interval :=
    hsub (Set.right_mem_Icc.mpr (by rw [RatIntervalCode.right]; linarith))
  have hθl := interpWeight_mem f n'.betting hc.width_pos hc.left_nonneg hc.right_le_one hl
  have hθr := interpWeight_mem f n'.betting hc.width_pos hc.left_nonneg hc.right_le_one hr
  have hθ := interpWeight_mono f n'.betting hc.width_pos hc.left_nonneg hc.right_le_one
    (s := n'.interval.left) (t := n'.interval.right) (by rw [RatIntervalCode.right]; linarith)
  simp only [interp, OscFrame.eval] at hLR ⊢
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hθl.1]
  · nlinarith
  · nlinarith [hθr.2]

theorem Step.mass_le {n n' : OscNode} (h : Inv f P n) (hs : Step f P n n') :
    n'.toOscFrame.mass f ≤ n.toOscFrame.mass f := by
  obtain ⟨h1, -, h3⟩ := hs.eval_nested f P h
  rw [OscFrame.mass, OscFrame.mass]
  linarith

/-- Every edge ending in waiting at most halves the width: an ordinary waiting child is a
binary child, and a regridding child into waiting carries the half-width condition. -/
theorem Step.two_mul_width_le_of_waiting {n n' : OscNode} (hs : Step f P n n')
    (hb : n'.betting = false) : 2 * n'.interval.width ≤ n.interval.width := by
  rcases hs.elim f P with ⟨b, -, rfl⟩ | ⟨c, -, hreg, rfl⟩
  · simp only [binaryNode, RatIntervalCode.width_child]
    linarith
  · have hnb : nextBetting f P n = false := hb
    rw [regridChild, Bool.and_eq_true] at hreg
    obtain ⟨-, hhalf⟩ := eligible_iff.mp hreg.1
    simp only [regridNode, AffineDyadicGrid.width_cellCode]
    rw [hnb] at hhalf ⊢
    exact hhalf rfl

/-- Every edge ending in waiting halves the mass. -/
theorem Step.mass_le_half_of_waiting {n n' : OscNode} (h : Inv f P n) (hs : Step f P n n')
    (hb : n'.betting = false) : n'.toOscFrame.mass f ≤ n.toOscFrame.mass f / 2 := by
  have hhalf := hs.two_mul_width_le_of_waiting f P hb
  have hLR := (h.connected.eval_lt f).le
  rw [OscFrame.mass, OscFrame.mass, hs.eval_eq f P h, hb]
  exact mass_le_half_of_width_le_half f h.connected.width_pos hhalf hLR

/-- Widths halve over every two edges. -/
theorem Step.two_mul_width_le {n n' n'' : OscNode} (h₁ : Step f P n n') (h₂ : Step f P n' n'') :
    2 * n''.interval.width ≤ n.interval.width := by
  have hle₂ := h₂.width_le f P
  have hle₁ := h₁.width_le f P
  rcases h₁.elim f P with ⟨b, -, rfl⟩ | ⟨c, -, -, rfl⟩
  · have hle₂' : n''.interval.width ≤ (n.interval.child b).width := hle₂
    rw [RatIntervalCode.width_child] at hle₂'
    linarith
  · cases hnb : nextBetting f P n
    · have hb : (regridNode (gridOf P (nextBetting f P n)) (nextBetting f P n) n c).betting
          = false := hnb
      have := h₁.two_mul_width_le_of_waiting f P hb
      linarith
    · -- the first edge regrids into betting; the second edge halves
      set n' := regridNode (gridOf P (nextBetting f P n)) (nextBetting f P n) n c with hn'
      have hb' : n'.betting = true := hnb
      have hcell : n'.cell.isSome = true := rfl
      rcases h₂.elim f P with ⟨b, -, rfl⟩ | ⟨c', hneed, -, rfl⟩
      · simp only [binaryNode, RatIntervalCode.width_child]
        linarith
      · have hsw : switched (nextBetting f P n') n' = true := by
          rw [needsRegrid, Bool.or_eq_true, hcell] at hneed
          simpa using hneed
        have hnb' : nextBetting f P n' = false := by
          rw [switched_iff, hb'] at hsw
          exact Bool.eq_false_iff.mpr hsw
        have hb'' : (regridNode (gridOf P (nextBetting f P n')) (nextBetting f P n') n' c').betting
            = false := hnb'
        have := h₂.two_mul_width_le_of_waiting f P hb''
        linarith

/-- Continuing into betting certifies the sample on the parent: it was resolved to betting. -/
theorem Step.nextBetting_of_betting {n n' : OscNode} (hs : Step f P n n')
    (hb : n'.betting = true) : nextBetting f P n = true := by
  rw [← hs.betting_eq_nextBetting f P]
  exact hb

/-- A betting resolution bounds the source slope over the interval by `γ + margin`. -/
theorem slope_le_of_nextBetting {n : OscNode} (hw : 0 < n.interval.width)
    (hn : nextBetting f P n = true) :
    slope f.addIdentity.toFun n.interval.left n.interval.right ≤ P.gamma + P.margin := by
  have herr := slopeCode_error f P n hw
  have hsample : ((RatCode.value (slopeCode f P n) : ℚ) : ℝ) ≤ P.gamma := by
    rw [nextBetting] at hn
    cases hb : n.betting
    · rw [hb, cond_false, RatCode.lt_iff, RatCode.value_ofNNRat] at hn
      have h1 : ((RatCode.value (slopeCode f P n) : ℚ) : ℝ) < P.beta := by
        rw [OscillationParams.beta]
        exact_mod_cast hn
      have := P.beta_add_margin_lt
      have := P.margin_pos
      linarith
    · rw [hb, cond_true, Bool.not_eq_true', RatCode.lt] at hn
      have hle : RatCode.le (slopeCode f P n) (RatCode.ofNNRat P.gammaCode) = true := by
        cases h : RatCode.le (slopeCode f P n) (RatCode.ofNNRat P.gammaCode)
        · rw [h] at hn
          exact absurd hn (by decide)
        · rfl
      rw [RatCode.le_iff, RatCode.value_ofNNRat] at hle
      rw [OscillationParams.gamma]
      exact_mod_cast hle
  have := (abs_le.mp herr).1
  linarith

end OscNode

/-! ## Paths -/

/-- An infinite path of successful steps from the root. -/
structure OscPath (f : ComputableMonotone) (P : OscillationParams) where
  /-- The nodes along the path. -/
  node : ℕ → OscNode
  /-- It starts at the root. -/
  node_zero : node 0 = OscNode.root
  /-- Consecutive nodes are joined by a successful step. -/
  step : ∀ k, OscNode.Step f P (node k) (node (k + 1))

namespace OscPath

variable {f : ComputableMonotone} {P : OscillationParams} (γ : OscPath f P)

theorem inv (k : ℕ) : OscNode.Inv f P (γ.node k) := by
  induction k with
  | zero => rw [γ.node_zero]; exact OscNode.Inv.root f P
  | succ k ih => exact ih.step f P (γ.step k)

theorem width_antitone : Antitone fun k ↦ (γ.node k).interval.width :=
  antitone_nat_of_succ_le fun k ↦ (γ.step k).width_le f P

theorem width_pos (k : ℕ) : 0 < (γ.node k).interval.width := (γ.inv k).connected.width_pos

theorem width_even_le (k : ℕ) : (γ.node (2 * k)).interval.width ≤ (2⁻¹ : ℝ) ^ k := by
  induction k with
  | zero => simp [γ.node_zero, OscNode.root, OscFrame.root]
  | succ k ih =>
    have h := (γ.step (2 * k)).two_mul_width_le f P (γ.step (2 * k + 1))
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
    linarith

theorem width_tendsto_zero : Tendsto (fun k ↦ (γ.node k).interval.width) atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ ↦ (2⁻¹ : ℝ) ^ (k / 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (Nat.tendsto_div_const_atTop (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
    (fun k ↦ (γ.width_pos k).le) fun k ↦ ?_
  calc (γ.node k).interval.width ≤ (γ.node (2 * (k / 2))).interval.width :=
        γ.width_antitone (Nat.mul_div_le k 2)
    _ ≤ (2⁻¹ : ℝ) ^ (k / 2) := γ.width_even_le _

theorem mass_antitone : Antitone fun k ↦ (γ.node k).toOscFrame.mass f :=
  antitone_nat_of_succ_le fun k ↦ (γ.step k).mass_le f P (γ.inv k)

theorem mass_pos (k : ℕ) : 0 < (γ.node k).toOscFrame.mass f := (γ.inv k).mass_pos f P

theorem mass_zero : (γ.node 0).toOscFrame.mass f = 1 := by
  rw [γ.node_zero]
  simp [OscFrame.mass, OscFrame.eval, OscNode.root, OscFrame.root]

/-- The number of waiting children among the first `k` edges. -/
def waitCount : ℕ → ℕ
  | 0 => 0
  | k + 1 => waitCount k + if (γ.node (k + 1)).betting = false then 1 else 0

theorem waitCount_monotone : Monotone γ.waitCount :=
  monotone_nat_of_le_succ fun k ↦ by
    change γ.waitCount k ≤ γ.waitCount k + _
    exact Nat.le_add_right _ _

theorem mass_le_pow_waitCount (k : ℕ) :
    (γ.node k).toOscFrame.mass f ≤ (2⁻¹ : ℝ) ^ γ.waitCount k := by
  induction k with
  | zero => rw [γ.mass_zero]; simp [waitCount]
  | succ k ih =>
    change (γ.node (k + 1)).toOscFrame.mass f ≤ (2⁻¹ : ℝ) ^ (γ.waitCount k + _)
    by_cases hb : (γ.node (k + 1)).betting = false
    · rw [if_pos hb, pow_succ]
      have := (γ.step k).mass_le_half_of_waiting f P (γ.inv k) hb
      linarith
    · rw [if_neg hb, add_zero]
      exact le_trans ((γ.step k).mass_le f P (γ.inv k)) ih

/-- With infinitely many waiting children, the count is unbounded. -/
theorem waitCount_tendsto_atTop (h : ∃ᶠ k in atTop, (γ.node (k + 1)).betting = false) :
    Tendsto γ.waitCount atTop atTop := by
  rw [Filter.frequently_atTop] at h
  have key : ∀ N : ℕ, ∃ k, N ≤ γ.waitCount k := by
    intro N
    induction N with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ N ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨j, hjk, hj⟩ := h k
      refine ⟨j + 1, ?_⟩
      change N + 1 ≤ γ.waitCount j + _
      rw [if_pos hj]
      have := γ.waitCount_monotone hjk
      omega
  exact tendsto_atTop_atTop.mpr fun N ↦
    let ⟨k, hk⟩ := key N
    ⟨k, fun k' hk' ↦ le_trans hk (γ.waitCount_monotone hk')⟩

/-- **Path mass convergence** (BMN Claim 4.4): along every infinite path the mass tends to zero,
with no point or witness involved. -/
theorem mass_tendsto_zero : Tendsto (fun k ↦ (γ.node k).toOscFrame.mass f) atTop (𝓝 0) := by
  by_cases hev : ∀ᶠ k in atTop, (γ.node (k + 1)).betting = true
  · -- eventually betting: the anchor is fixed and the next edge certifies the slope
    rw [Filter.eventually_atTop] at hev
    obtain ⟨k₀, hk₀⟩ := hev
    -- from `k₀ + 1` on, every node is betting and the anchor is constant
    have hbet : ∀ k, k₀ + 1 ≤ k → (γ.node k).betting = true := fun k hk ↦ by
      have hk' : k = (k - 1) + 1 := by omega
      rw [hk']
      exact hk₀ (k - 1) (by omega)
    have hanchor : ∀ k, k₀ + 1 ≤ k → (γ.node k).phaseStart = (γ.node (k₀ + 1)).phaseStart := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.lt_or_ge k (k₀ + 1) with hlt | hge
        · have : k = k₀ := by omega
          subst this
          rfl
        · rw [← ih hge]
          exact (γ.step k).anchor_eq_of_not_switched f P (by rw [hbet _ hge, hbet _ (by omega)])
    set A := (γ.node (k₀ + 1)).phaseStart with hA
    have hAconn := (γ.inv (k₀ + 1)).anchor_connected
    have hFA : 0 < f.addIdentity.toFun A.interval.right - f.addIdentity.toFun A.interval.left := by
      linarith [width_le_addIdentity_gap f hAconn.left_nonneg hAconn.right_le_one,
        hAconn.width_pos]
    set C : ℝ := A.mass f / (f.addIdentity.toFun A.interval.right
      - f.addIdentity.toFun A.interval.left) * (P.gamma + P.margin) with hC
    have hbound : ∀ k, k₀ + 1 ≤ k →
        (γ.node k).toOscFrame.mass f ≤ C * (γ.node k).interval.width := by
      intro k hk
      have hinv := γ.inv k
      have hid := hinv.mass_betting f P (hbet k hk)
      rw [hanchor k hk] at hid
      have hslope := OscNode.slope_le_of_nextBetting f P (γ.width_pos k)
        ((γ.step k).nextBetting_of_betting f P (hbet (k + 1) (by omega)))
      have hw := γ.width_pos k
      have hwidth : (γ.node k).interval.right - (γ.node k).interval.left
          = (γ.node k).interval.width := by rw [RatIntervalCode.right]; ring
      rw [slope_def_field, hwidth, div_le_iff₀ hw] at hslope
      have hmassA : 0 < A.mass f := by
        rw [OscFrame.mass, OscFrame.eval]
        exact sub_pos.mpr (hAconn.eval_lt f)
      rw [hC, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hFA, hid]
      have := mul_le_mul_of_nonneg_left hslope hmassA.le
      linarith
    have hC0 : Tendsto (fun k ↦ C * (γ.node k).interval.width) atTop (𝓝 0) := by
      simpa using γ.width_tendsto_zero.const_mul C
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC0
      (Filter.Eventually.of_forall fun k ↦ (γ.mass_pos k).le) ?_
    rw [Filter.eventually_atTop]
    exact ⟨k₀ + 1, hbound⟩
  · -- infinitely many waiting children: each halves the mass
    have hfreq : ∃ᶠ k in atTop, (γ.node (k + 1)).betting = false := by
      have := Filter.not_eventually.mp hev
      simpa only [Bool.not_eq_true] using this
    have hcount := γ.waitCount_tendsto_atTop hfreq
    have hpow : Tendsto (fun k ↦ (2⁻¹ : ℝ) ^ γ.waitCount k) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hcount
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
      (fun k ↦ (γ.mass_pos k).le) γ.mass_le_pow_waitCount

end OscPath

end AlgorithmicRandomness
