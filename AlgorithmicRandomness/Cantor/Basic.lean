/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Cantor space, bit strings, and cylinders

The basic objects of algorithmic randomness on fair-coin Cantor space:

* `AlgorithmicRandomness.BitString`: finite binary strings, as `List Bool`;
* `AlgorithmicRandomness.Cantor`: infinite binary sequences, as `ℕ → Bool`;
* `AlgorithmicRandomness.cylinder σ`: the basic clopen set of sequences extending `σ`.

The main results are the combinatorics of cylinders — inclusion is contravariant prefix
extension (`cylinder_subset_cylinder_iff`), disjointness is incompatibility
(`disjoint_cylinder_iff`), the children decomposition (`cylinder_eq_union_concat`) — and the
bridge `cylinder_eq_measureTheory_cylinder` to mathlib's finite-coordinate
`MeasureTheory.cylinder`, through which cylinders are shown clopen and measurable.
-/

namespace AlgorithmicRandomness

/-- Finite binary strings, the vertices of the full binary tree `2^{<ω}`. -/
abbrev BitString := List Bool

/-- Cantor space `2^ω`: infinite binary sequences. -/
abbrev Cantor := ℕ → Bool

namespace BitString

/-- Two strings are compatible if one is a prefix of the other, equivalently if some sequence
extends both. -/
def Compatible (σ τ : BitString) : Prop := σ <+: τ ∨ τ <+: σ

instance : DecidableRel Compatible := fun σ τ ↦
  inferInstanceAs (Decidable (σ <+: τ ∨ τ <+: σ))

theorem Compatible.symm {σ τ : BitString} (h : Compatible σ τ) : Compatible τ σ := Or.symm h

theorem compatible_comm {σ τ : BitString} : Compatible σ τ ↔ Compatible τ σ :=
  ⟨Compatible.symm, Compatible.symm⟩

/-- `σ` is an initial segment of the infinite sequence `x`. -/
def IsPrefixOf (σ : BitString) (x : Cantor) : Prop := ∀ i : Fin σ.length, x i = σ[i]

/-- A string is a prefix of any longer string with which it agrees where both are defined. -/
theorem prefix_of_agree {σ τ : BitString} (hle : σ.length ≤ τ.length)
    (h : ∀ (i : ℕ) (hi : i < σ.length) (hj : i < τ.length), σ[i] = τ[i]) : σ <+: τ := by
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by simp [hle]) fun i hi₁ hi₂ ↦ ?_
  rw [List.getElem_take]
  exact h i hi₁ (lt_of_lt_of_le hi₁ hle)

/-- If two strings agree wherever both are defined, one is a prefix of the other. -/
theorem compatible_of_agree {σ τ : BitString}
    (h : ∀ (i : ℕ) (hi : i < σ.length) (hj : i < τ.length), σ[i] = τ[i]) : Compatible σ τ := by
  rcases le_total σ.length τ.length with hle | hle
  · exact Or.inl (prefix_of_agree hle h)
  · exact Or.inr (prefix_of_agree hle fun i hi hj ↦ (h i hj hi).symm)

end BitString

/-- The basic clopen set of all infinite sequences extending the finite string `σ`. -/
def cylinder (σ : BitString) : Set Cantor := {x | BitString.IsPrefixOf σ x}

@[simp]
theorem mem_cylinder_iff {σ : BitString} {x : Cantor} :
    x ∈ cylinder σ ↔ ∀ i : Fin σ.length, x i = σ[i] :=
  Iff.rfl

@[simp]
theorem cylinder_nil : cylinder ([] : BitString) = Set.univ := by
  ext x
  simp [mem_cylinder_iff]

theorem cylinder_nonempty (σ : BitString) : (cylinder σ).Nonempty :=
  ⟨fun i ↦ σ.getD i false, fun i ↦ List.getD_eq_getElem σ false i.isLt⟩

theorem cylinder_anti {σ τ : BitString} (h : σ <+: τ) : cylinder τ ⊆ cylinder σ := by
  intro x hx i
  obtain ⟨ρ, rfl⟩ := h
  have hi : (i : ℕ) < (σ ++ ρ).length := lt_of_lt_of_le i.isLt (by simp)
  simpa [List.getElem_append_left i.isLt] using hx ⟨i, hi⟩

/-- Cylinder inclusion is contravariant prefix extension. -/
theorem cylinder_subset_cylinder_iff {σ τ : BitString} : cylinder τ ⊆ cylinder σ ↔ σ <+: τ := by
  refine ⟨fun hsub ↦ ?_, cylinder_anti⟩
  rcases le_or_gt σ.length τ.length with hle | hlt
  · -- the canonical extension of `τ` lies in `cylinder σ`, so `σ` and `τ` agree on `σ`'s domain
    have hxτ : (fun i ↦ τ.getD i false) ∈ cylinder τ :=
      fun i ↦ List.getD_eq_getElem τ false i.isLt
    have hxσ := hsub hxτ
    exact BitString.prefix_of_agree hle fun i hi hj ↦
      (hxσ ⟨i, hi⟩).symm.trans (List.getD_eq_getElem τ false hj)
  · -- otherwise an extension of `τ` disagreeing with `σ` at coordinate `τ.length` gives a
    -- contradiction
    have hyτ : (fun i ↦ if h : i < τ.length then τ[i] else !(σ.getD i false)) ∈ cylinder τ :=
      fun i ↦ dif_pos i.isLt
    have hyσ := hsub hyτ ⟨τ.length, hlt⟩
    simp only [dif_neg (lt_irrefl τ.length), List.getD_eq_getElem σ false hlt] at hyσ
    simp at hyσ

theorem cylinder_inter_of_prefix {σ τ : BitString} (h : σ <+: τ) :
    cylinder σ ∩ cylinder τ = cylinder τ :=
  Set.inter_eq_right.mpr (cylinder_anti h)

/-- Cylinders on incompatible strings are disjoint; compatible ones are nested. -/
theorem disjoint_cylinder_iff {σ τ : BitString} :
    Disjoint (cylinder σ) (cylinder τ) ↔ ¬BitString.Compatible σ τ := by
  constructor
  · rintro hd (h | h)
    · obtain ⟨x, hx⟩ := cylinder_nonempty τ
      exact Set.disjoint_left.mp hd (cylinder_anti h hx) hx
    · obtain ⟨x, hx⟩ := cylinder_nonempty σ
      exact Set.disjoint_left.mp hd hx (cylinder_anti h hx)
  · intro hc
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hc (BitString.compatible_of_agree fun i hi hj ↦
      (hx ⟨i, hi⟩).symm.trans (hx' ⟨i, hj⟩))

/-- A cylinder splits into its two children. -/
theorem cylinder_eq_union_concat (σ : BitString) :
    cylinder σ = cylinder (σ ++ [false]) ∪ cylinder (σ ++ [true]) := by
  apply Set.Subset.antisymm
  · intro x hx
    have key : ∀ b : Bool, x σ.length = b → x ∈ cylinder (σ ++ [b]) := by
      intro b hb i
      obtain ⟨i, hilt⟩ := i
      simp only [Fin.getElem_fin]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hilt) with hi | hi
      · rw [List.getElem_append_left hi]
        exact hx ⟨i, hi⟩
      · subst hi
        rw [List.getElem_concat_length]
        exacts [hb, rfl]
    cases hb : x σ.length
    · exact Or.inl (key false hb)
    · exact Or.inr (key true hb)
  · rintro x (hx | hx) <;> exact cylinder_anti (List.prefix_append σ _) hx

section Bridge

/-- The restriction of `σ` to `Finset.range σ.length`, in the form expected by mathlib's
finite-coordinate `MeasureTheory.cylinder`. -/
def BitString.rangeRestriction (σ : BitString) (i : Finset.range σ.length) : Bool :=
  σ[(i : ℕ)]'(Finset.mem_range.mp i.2)

/-- Our prefix cylinders are mathlib's finite-coordinate cylinders on a singleton. -/
theorem cylinder_eq_measureTheory_cylinder (σ : BitString) :
    cylinder σ = MeasureTheory.cylinder (α := fun _ : ℕ ↦ Bool) (Finset.range σ.length)
      {BitString.rangeRestriction σ} := by
  ext x
  simp only [MeasureTheory.mem_cylinder, Set.mem_singleton_iff, funext_iff, mem_cylinder_iff]
  constructor
  · intro hx i
    exact hx ⟨(i : ℕ), Finset.mem_range.mp i.2⟩
  · intro hx i
    exact hx ⟨(i : ℕ), Finset.mem_range.mpr i.isLt⟩

end Bridge

section Topology

/-- A cylinder is the finite intersection of one-coordinate constraints. -/
theorem cylinder_eq_iInter (σ : BitString) :
    cylinder σ = ⋂ i : Fin σ.length, (fun x : Cantor ↦ x i) ⁻¹' {σ[i]} := by
  ext x
  simp [mem_cylinder_iff]

theorem isClopen_cylinder (σ : BitString) : IsClopen (cylinder σ) := by
  rw [cylinder_eq_iInter]
  refine ⟨isClosed_iInter fun i ↦ ?_, isOpen_iInter_of_finite fun i ↦ ?_⟩
  · exact (isClosed_discrete _).preimage (continuous_apply _)
  · exact (isOpen_discrete _).preimage (continuous_apply _)

theorem measurableSet_cylinder (σ : BitString) : MeasurableSet (cylinder σ) := by
  rw [cylinder_eq_iInter]
  exact MeasurableSet.iInter fun i ↦ measurable_pi_apply _ (measurableSet_singleton _)

end Topology

end AlgorithmicRandomness
