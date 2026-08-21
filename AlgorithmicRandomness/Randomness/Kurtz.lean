/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.EffectiveClosed.ComputableTree
import AlgorithmicRandomness.Randomness.ComputableImpliesSchnorr
import AlgorithmicRandomness.Randomness.ComputablePoint

/-!
# Kurtz randomness

A point is Kurtz random when it avoids every null effectively closed class:

```text
IsKurtzRandom x  ↔  ∀ T : ComputableTree, fairCoin T.paths = 0 → x ∉ T.paths
```

This is the weakest notion in the library. Nullity is a hypothesis consumed only at this one
definition, so it stays a proposition rather than becoming a bundled field.

The implication from Schnorr randomness is not a new construction: a null computable tree already
carries a Schnorr test whose levels are its own level covers, and whose capture set contains every
path. Computable and Martin-Löf randomness are then derived through Schnorr randomness rather than
reproved.

The sanity check — that no computable point is Kurtz random — cannot be inherited from the
corresponding fact for Schnorr randomness, since Kurtz randomness is the *weaker* notion and that
implication runs the wrong way. It needs its own witness: the tree whose nodes are the prefixes of
the point, whose path set is the singleton, and whose membership test compares the finitely many
bits of a string against the bundled point program.
-/

open MeasureTheory

namespace AlgorithmicRandomness

/-! ## The prefix tree of a computable point -/

namespace ComputableCantorPoint

/-- Whether the first `k` bits of `σ` agree with the point. The bound is what keeps this
executable: it consults the point program at finitely many positions and never searches. -/
def agreeUpto (p : ComputableCantorPoint) (σ : BitString) : ℕ → Bool
  | 0 => true
  | k + 1 => agreeUpto p σ k && (σ.getD k false == p.point k)

variable (p : ComputableCantorPoint)

theorem agreeUpto_eq_true_iff {σ : BitString} {k : ℕ} :
    p.agreeUpto σ k = true ↔ ∀ i < k, σ.getD i false = p.point i := by
  induction k with
  | zero => simp [agreeUpto]
  | succ k ih =>
    rw [agreeUpto, Bool.and_eq_true, ih, beq_iff_eq]
    constructor
    · rintro ⟨h, hk⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hk
    · exact fun h ↦ ⟨fun i hi ↦ h i (Nat.lt_succ_of_lt hi), h k (Nat.lt_succ_self k)⟩

/-- The membership test of the prefix tree: every bit of `σ` agrees with the point. -/
def prefixMember (σ : BitString) : Bool := p.agreeUpto σ σ.length

theorem prefixMember_eq_true_iff {σ : BitString} :
    p.prefixMember σ = true ↔ p.point ∈ cylinder σ := by
  rw [prefixMember, agreeUpto_eq_true_iff, mem_cylinder_iff]
  constructor
  · intro h i
    rw [Fin.getElem_fin, ← List.getD_eq_getElem σ false i.isLt]
    exact (h i i.isLt).symm
  · intro h i hi
    rw [List.getD_eq_getElem σ false hi]
    exact (h ⟨i, hi⟩).symm

private theorem agreeUpto_eq_natRec (σ : BitString) (k : ℕ) :
    p.agreeUpto σ k
      = Nat.rec (motive := fun _ ↦ Bool) true
        (fun i acc ↦ acc && (σ.getD i false == p.point i)) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [agreeUpto, ih]

theorem computable_prefixMember : Computable p.prefixMember := by
  have hstep : Computable fun w : BitString × (ℕ × Bool) ↦
      (w.2.2 && (w.1.getD w.2.1 false == p.point w.2.1)) := by
    have hbit : Computable fun w : BitString × (ℕ × Bool) ↦ p.point w.2.1 :=
      p.computable_point.comp (Computable.fst.comp Computable.snd)
    have hsig : Computable fun w : BitString × (ℕ × Bool) ↦ w.1.getD w.2.1 false :=
      ((Primrec.list_getD false).comp Primrec.fst (Primrec.fst.comp Primrec.snd)).to_comp
    have heq : Computable fun q : Bool × Bool ↦ (q.1 == q.2) :=
      (primrecPred_iff_primrec_decide.mp Primrec.eq).to_comp
    exact (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (heq.comp (Computable.pair hsig hbit)))
  refine (Computable.nat_rec (f := fun σ : BitString ↦ σ.length)
    (g := fun _ : BitString ↦ true) Primrec.list_length.to_comp (Computable.const true)
    hstep.to₂).of_eq fun σ ↦ ?_
  rw [prefixMember, agreeUpto_eq_natRec]

private theorem computable_prefixMemberFun : Computable fun n : ℕ ↦
    Encodable.encode (p.prefixMember ((Encodable.decode (α := BitString) n).getD [])) :=
  (Computable.encode.comp (p.computable_prefixMember.comp
    (Primrec.option_getD.comp Primrec.decode (Primrec.const [])).to_comp))

/-- **The prefix tree.** Its nodes are the strings the point extends. -/
noncomputable def prefixTree : ComputableTree where
  nodes := {σ | p.point ∈ cylinder σ}
  prefix_closed hσ hτ := cylinder_anti hτ hσ
  member := p.prefixMember
  member_iff _ := p.prefixMember_eq_true_iff
  program := NatFunctionCode.ofComputable p.computable_prefixMemberFun
  eval_member σ := by
    rw [NatFunctionCode.ofComputable_toFun, Encodable.encodek, Option.getD_some]

@[simp] theorem mem_nodes_prefixTree_iff {σ : BitString} :
    σ ∈ p.prefixTree.toCantorTree.nodes ↔ p.point ∈ cylinder σ := Iff.rfl

/-- The path set is exactly the point: a sequence all of whose initial segments the point extends
agrees with the point everywhere. -/
theorem mem_paths_prefixTree_iff {x : Cantor} :
    x ∈ p.prefixTree.paths ↔ x = p.point := by
  constructor
  · intro hx
    funext i
    have hcyl : p.point ∈ cylinder (initSeg x (i + 1)) := hx (i + 1)
    have hlt : i < (initSeg x (i + 1)).length := by rw [length_initSeg]; omega
    have hbit := mem_cylinder_iff.mp hcyl ⟨i, hlt⟩
    simp only [initSeg, Fin.getElem_fin, List.getElem_ofFn] at hbit
    exact hbit.symm
  · rintro rfl
    exact fun n ↦ mem_cylinder_initSeg p.point n

theorem paths_prefixTree : p.prefixTree.paths = {p.point} := by
  ext x
  rw [mem_paths_prefixTree_iff, Set.mem_singleton_iff]

theorem fairCoin_paths_prefixTree : fairCoin p.prefixTree.paths = 0 := by
  rw [paths_prefixTree, fairCoin_singleton]

end ComputableCantorPoint

/-! ## Kurtz randomness -/

/-- A point is Kurtz random when it avoids every null effectively closed class. -/
def IsKurtzRandom (x : Cantor) : Prop :=
  ∀ T : ComputableTree, fairCoin T.paths = 0 → x ∉ T.paths

theorem not_isKurtzRandom_of_mem_paths {T : ComputableTree} {x : Cantor}
    (hnull : fairCoin T.paths = 0) (hx : x ∈ T.paths) : ¬IsKurtzRandom x :=
  fun h ↦ h T hnull hx

/-- **Schnorr randomness implies Kurtz randomness.** The Schnorr test is the one the null tree
already carries; nothing is constructed here. -/
theorem IsSchnorrRandom.isKurtzRandom {x : Cantor} (hx : IsSchnorrRandom x) :
    IsKurtzRandom x := by
  intro T hnull hpath
  exact hx (T.nullSchnorrTest hnull) (T.captures_nullSchnorrTest hnull hpath)

theorem IsComputablyRandom.isKurtzRandom {x : Cantor} (hx : IsComputablyRandom x) :
    IsKurtzRandom x := hx.isSchnorrRandom.isKurtzRandom

theorem IsMartinLofRandom.isKurtzRandom {x : Cantor} (hx : IsMartinLofRandom x) :
    IsKurtzRandom x := hx.isSchnorrRandom.isKurtzRandom

/-! ## No computable point is Kurtz random -/

/-- The sanity check at the bottom of the hierarchy. Since Kurtz randomness is the weakest notion,
this does not follow from the corresponding facts above it and needs its own witness. -/
theorem ComputableCantorPoint.not_isKurtzRandom (p : ComputableCantorPoint) :
    ¬IsKurtzRandom p.point :=
  not_isKurtzRandom_of_mem_paths p.fairCoin_paths_prefixTree
    (by rw [p.paths_prefixTree]; exact Set.mem_singleton _)

end AlgorithmicRandomness
