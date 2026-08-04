/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Cantor.FiniteOpen
import AlgorithmicRandomness.Coding.Partrec

/-!
# Coded uniformly c.e. open sets

A `UniformOpenCode` is one partial recursive program, read as naming a uniformly c.e. family
of open subsets of Cantor space: on paired input `Nat.pair n k` it enumerates strings into
the `n`-th set. The wrapper is nominal and carries no proof fields — a raw `Code` is
computation syntax, a `UniformOpenCode` asserts how that syntax is interpreted — and there is
deliberately no coercion, so the boundary stays visible at every use site.

This file provides the single bridge

  program → finite stages → open set → canonical increasing exact measure approximation.

The stages `stage`, `stageSet`, `stageWeight` are cumulative; `denote` is their increasing
union; and the two measure theorems are `fairCoin_stageSet` (each stage has an exact `ℚ≥0`
measure) and `fairCoin_denote` (the measure of the open set is the supremum of those exact
stage measures, by continuity from below). Every c.e. open therefore comes with a canonical
computable lower approximation by construction.

Stages are proof-oriented approximations, not performance promises: `Code.evaln`'s fuel
argument guards every recursive call by `input ≤ fuel`, so fuel demands grow with the
*values* a program pairs, not with its running time. The fuel constants in the examples below
are experimental facts about that guard.

Code transformations, unions, reindexing, measure bounds, and trimming are deliberately out
of scope here.
-/

open MeasureTheory
open scoped NNRat ENNReal

namespace AlgorithmicRandomness

/-- A code for a uniformly c.e. family of open subsets of Cantor space: one program, read as
enumerating strings into the `n`-th set on paired inputs `Nat.pair n k`. No proof fields. -/
structure UniformOpenCode where
  /-- The underlying partial recursive program. -/
  program : Nat.Partrec.Code

namespace UniformOpenCode

@[ext]
theorem ext {e₁ e₂ : UniformOpenCode} (h : e₁.program = e₂.program) : e₁ = e₂ := by
  cases e₁; cases e₂; congr

variable (e : UniformOpenCode) (n s : ℕ)

/-! ## Stages -/

/-- The finite stage: strings enumerated into the `n`-th set by stage `s`. -/
def stage : Finset BitString := stringStage e.program n s

/-- The finite open set reached by stage `s`. -/
def stageSet : Set Cantor := cylinderUnion (e.stage n s)

/-- The exact `ℚ≥0` measure of stage `s`. Executable. -/
def stageWeight : ℚ≥0 := finiteOpenWeight (e.stage n s)

/-- The `n`-th open set denoted by `e`: the increasing union of its finite stages. -/
def denote : Set Cantor := ⋃ s, e.stageSet n s

variable {e n s}

/-! ## Monotonicity -/

theorem stage_mono {t : ℕ} (h : s ≤ t) : e.stage n s ⊆ e.stage n t :=
  stringStage_mono h

theorem stageSet_mono {t : ℕ} (h : s ≤ t) : e.stageSet n s ⊆ e.stageSet n t :=
  cylinderUnion_mono (stage_mono h)

theorem stageWeight_mono {t : ℕ} (h : s ≤ t) : e.stageWeight n s ≤ e.stageWeight n t :=
  finiteOpenWeight_mono (stage_mono h)

theorem monotone_stageSet (e : UniformOpenCode) (n : ℕ) : Monotone (e.stageSet n) :=
  fun _ _ h ↦ stageSet_mono h

/-! ## Membership -/

theorem mem_stageSet {x : Cantor} :
    x ∈ e.stageSet n s ↔ ∃ σ ∈ e.stage n s, x ∈ cylinder σ :=
  mem_cylinderUnion

@[simp]
theorem mem_denote {x : Cantor} : x ∈ e.denote n ↔ ∃ s, x ∈ e.stageSet n s := by
  simp [denote]

/-- The staged open set is the semantic one: `x` lies in the `n`-th set exactly when some
string enumerated at index `n` is a prefix of `x`. -/
theorem mem_denote_iff_enumerates {x : Cantor} :
    x ∈ e.denote n ↔ ∃ σ, EnumeratesString e.program n σ ∧ x ∈ cylinder σ := by
  rw [mem_denote]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨σ, hσ, hxσ⟩ := mem_stageSet.mp hs
    exact ⟨σ, stringStage_sound hσ, hxσ⟩
  · rintro ⟨σ, hσ, hxσ⟩
    obtain ⟨s, hs⟩ := stringStage_complete hσ
    exact ⟨s, mem_stageSet.mpr ⟨σ, hs, hxσ⟩⟩

/-! ## Topology and measurability -/

theorem isOpen_stageSet (e : UniformOpenCode) (n s : ℕ) : IsOpen (e.stageSet n s) :=
  isOpen_biUnion fun σ _ ↦ (isClopen_cylinder σ).isOpen

theorem isOpen_denote (e : UniformOpenCode) (n : ℕ) : IsOpen (e.denote n) :=
  isOpen_iUnion fun s ↦ isOpen_stageSet e n s

theorem measurableSet_stageSet (e : UniformOpenCode) (n s : ℕ) :
    MeasurableSet (e.stageSet n s) :=
  measurableSet_cylinderUnion (e.stage n s)

theorem measurableSet_denote (e : UniformOpenCode) (n : ℕ) : MeasurableSet (e.denote n) :=
  MeasurableSet.iUnion fun s ↦ measurableSet_stageSet e n s

theorem stageSet_subset_denote (e : UniformOpenCode) (n s : ℕ) :
    e.stageSet n s ⊆ e.denote n :=
  Set.subset_iUnion (e.stageSet n) s

/-- A point of a coded c.e. open set has a whole cylinder around it inside the set: the set is
open, and the witnessing cylinder is one that was actually enumerated. -/
theorem exists_cylinder_subset_denote {e : UniformOpenCode} {n : ℕ} {x : Cantor}
    (hx : x ∈ e.denote n) : ∃ σ, x ∈ cylinder σ ∧ cylinder σ ⊆ e.denote n := by
  obtain ⟨s, hs⟩ := mem_denote.mp hx
  obtain ⟨σ, hσ, hxσ⟩ := mem_stageSet.mp hs
  refine ⟨σ, hxσ, ?_⟩
  refine subset_trans ?_ (stageSet_subset_denote e n s)
  exact Set.subset_biUnion_of_mem (u := fun τ ↦ cylinder τ) hσ

/-! ## Measure -/

/-- Each finite stage has an exact rational measure. -/
theorem fairCoin_stageSet (e : UniformOpenCode) (n s : ℕ) :
    fairCoin (e.stageSet n s) = (e.stageWeight n s : ℝ≥0∞) :=
  fairCoin_cylinderUnion (e.stage n s)

/-- Continuity from below: the measure of a c.e. open set is the supremum of the exact
measures of its finite stages. This is the canonical increasing lower approximation. -/
theorem fairCoin_denote (e : UniformOpenCode) (n : ℕ) :
    fairCoin (e.denote n) = ⨆ s, (e.stageWeight n s : ℝ≥0∞) := by
  rw [denote, (monotone_stageSet e n).measure_iUnion]
  exact iSup_congr fun s ↦ fairCoin_stageSet e n s

/-- A semantic measure bound on a c.e. open set is exactly a uniform bound on its exact finite
stage measures. Used in both directions: semantic bounds give finite-stage bounds, and
constructions that enforce finite-stage bounds recover the semantic bound. -/
theorem fairCoin_denote_le_iff (e : UniformOpenCode) (n : ℕ) (q : ℝ≥0∞) :
    fairCoin (e.denote n) ≤ q ↔ ∀ s, (e.stageWeight n s : ℝ≥0∞) ≤ q := by
  rw [fairCoin_denote, iSup_le_iff]

/-! ## Acceptance example -/

/-- The uniform family of prefix cylinders of the constant-`true` point: at index `n` it
enumerates exactly the string `true^n`. -/
def replicateTrueOpen : UniformOpenCode := ⟨replicateTrueFamilyCode⟩

theorem denote_replicateTrueOpen (n : ℕ) :
    replicateTrueOpen.denote n = cylinder (List.replicate n true) := by
  ext x
  rw [mem_denote_iff_enumerates]
  constructor
  · rintro ⟨σ, hσ, hxσ⟩
    rwa [enumeratesString_replicateTrueFamilyCode.mp hσ] at hxσ
  · intro hx
    exact ⟨List.replicate n true, enumeratesString_replicateTrueFamilyCode.mpr rfl, hx⟩

theorem fairCoin_denote_replicateTrueOpen (n : ℕ) :
    fairCoin (replicateTrueOpen.denote n) = 2⁻¹ ^ n := by
  rw [denote_replicateTrueOpen, fairCoin_cylinder, List.length_replicate]

section Examples
-- the approximation becoming exact: the stage is empty until it saturates, after which the
-- exact weight is the measure of the limit open set
set_option linter.hashCommand false

#guard replicateTrueOpen.stageWeight 2 3 = 0
#guard replicateTrueOpen.stageWeight 2 101 = 1 / 4

end Examples

end UniformOpenCode

end AlgorithmicRandomness
