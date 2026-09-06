/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Partrec

/-!
# A computable left fold over lists

Mathlib has `Primrec.list_foldl` but no `Computable` analogue. The fold is recovered from
`Computable.nat_rec` on the length: the `n`-th stage folds the first `n` elements, reading the
`n`-th element with `List.getElem?`, and the result is read off at the full length.
-/

namespace Computable

/-- The stage-`n` fold: the first `n` elements of the list have been consumed. -/
private theorem foldl_take_succ {β σ : Type*} (l : List β) (h : σ → β → σ) (s : σ) (n : ℕ) :
    (l.take (n + 1)).foldl h s =
      match l[n]? with
      | some b => h ((l.take n).foldl h s) b
      | none => (l.take n).foldl h s := by
  rw [List.take_add_one, List.foldl_append]
  rcases l[n]? with - | b <;> rfl

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a ↦ (f a).foldl (fun s b ↦ h a (s, b)) (g a) := by
  have hstage : Computable fun a ↦
      Nat.rec (motive := fun _ ↦ σ) (g a)
        (fun n IH ↦
          match (f a)[n]? with
          | some b => h a (IH, b)
          | none => IH)
        (f a).length := by
    refine nat_rec (h := fun (a : α) (q : ℕ × σ) ↦
      match (f a)[q.1]? with
      | some b => h a (q.2, b)
      | none => q.2) (list_length.comp hf) hg ?_
    have hget : Computable fun p : α × ℕ × σ ↦ (f p.1)[p.2.1]? :=
      list_getElem?.comp (hf.comp fst) (fst.comp snd)
    have hsome : Computable₂ fun (p : α × ℕ × σ) (b : β) ↦ h p.1 (p.2.2, b) :=
      hh.comp (fst.comp fst) (pair (snd.comp (snd.comp fst)) snd)
    exact (option_casesOn hget (snd.comp snd) hsome).of_eq fun p ↦ by
      cases hp : (f p.1)[p.2.1]? <;> simp [hp]
  refine hstage.of_eq fun a ↦ ?_
  have key : ∀ n : ℕ,
      Nat.rec (motive := fun _ ↦ σ) (g a)
        (fun n IH ↦
          match (f a)[n]? with
          | some b => h a (IH, b)
          | none => IH) n = ((f a).take n).foldl (fun s b ↦ h a (s, b)) (g a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [foldl_take_succ]
      simp only [ih]
  rw [key, List.take_length]

end Computable
