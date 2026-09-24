/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.LipschitzRandomness
import AlgorithmicRandomness.Analysis.MonotoneOscillation

/-!
# Computable randomness is differentiability

This file is composition only. It assembles two characterizations of computable randomness of a
real `z ∈ [0, 1]`:

* every `ComputableMonotone` is differentiable at `z` (Brattka–Miller–Nies, arXiv:1104.4465);
* every `ComputableLipschitz` is differentiable at `z` (Freer–Kjos-Hanssen–Nies–Stephan,
  arXiv:1402.2429, Theorem 4.2).

The ingredients are the monotone forward direction (`IsComputablyRandomReal.differentiableAt`),
the Lipschitz reverse direction (`isComputablyRandomReal_of_forall_differentiableAt`), and the
interior bridge `differentiableAt_toComputableMonotone_iff` between the two presentations. The
bridge is used only in the interior. The endpoints are settled separately: a random real is
irrational, so it is never `0` or `1`, and at `0` and `1` the clamped identity `clampId` is a
monotone function that is not differentiable.

## Scope

The statements are about the library's two presentations, and should be read against them:
`ComputableMonotone` is a continuous nondecreasing function on `[0, 1]` with a program
approximating its values at rational arguments, and `ComputableLipschitz` is a Lipschitz function
with a natural bound and exact rational values at the dyadic cut points. Both are extended to `ℝ`
by clamping.

The unit-interval hypothesis cannot be dropped. Outside `[0, 1]` every such extension is locally
constant, so universal differentiability holds there (`differentiableAt_toFun_of_notMem`), while
randomness fails (`IsComputablyRandomReal.mem_unit`).
-/

namespace AlgorithmicRandomness

/-- A computably random real lies in the open unit interval. -/
theorem IsComputablyRandomReal.mem_Ioo {z : ℝ} (hz : IsComputablyRandomReal z) :
    z ∈ Set.Ioo (0 : ℝ) 1 := by
  have hz01 := hz.mem_unit
  exact ⟨lt_of_le_of_ne hz01.1 fun h ↦ hz.ne_rat 0 (by rw [← h]; norm_num),
    lt_of_le_of_ne hz01.2 fun h ↦ hz.ne_rat 1 (by rw [h]; norm_num)⟩

/-- **Randomness ⇒ Lipschitz differentiability.** At a computably random real, every computable
Lipschitz function is differentiable. -/
theorem IsComputablyRandomReal.differentiableAt_lipschitz (f : ComputableLipschitz) {z : ℝ}
    (hz : IsComputablyRandomReal z) : DifferentiableAt ℝ f.toFun z :=
  (f.differentiableAt_toComputableMonotone_iff hz.mem_Ioo).mp
    (hz.differentiableAt f.toComputableMonotone)

/-- **Universal monotone differentiability ⇒ randomness.** The endpoints are excluded by the
clamped identity; in the interior, each computable Lipschitz function is differentiable through
its monotone presentation, and the Lipschitz reverse direction applies. -/
theorem isComputablyRandomReal_of_forall_monotone_differentiableAt {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ g : ComputableMonotone, DifferentiableAt ℝ g.toFun z) :
    IsComputablyRandomReal z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact ComputableMonotone.not_differentiableAt_clampId_zero (h _)
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact ComputableMonotone.not_differentiableAt_clampId_one (h _)
  have hzI : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hz.1 hz0.symm, lt_of_le_of_ne hz.2 hz1⟩
  exact isComputablyRandomReal_of_forall_differentiableAt hz fun f ↦
    (f.differentiableAt_toComputableMonotone_iff hzI).mp (h _)

/-- **Brattka–Miller–Nies.** A real of `[0, 1]` is computably random exactly when every
computable nondecreasing function is differentiable there. -/
theorem isComputablyRandomReal_iff_forall_computableMonotone {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    IsComputablyRandomReal z ↔ ∀ g : ComputableMonotone, DifferentiableAt ℝ g.toFun z :=
  ⟨fun hr g ↦ hr.differentiableAt g, isComputablyRandomReal_of_forall_monotone_differentiableAt hz⟩

/-- **Freer–Kjos-Hanssen–Nies–Stephan.** A real of `[0, 1]` is computably random exactly when
every computable Lipschitz function is differentiable there. -/
theorem isComputablyRandomReal_iff_forall_computableLipschitz {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    IsComputablyRandomReal z ↔ ∀ f : ComputableLipschitz, DifferentiableAt ℝ f.toFun z :=
  ⟨fun hr f ↦ hr.differentiableAt_lipschitz f, isComputablyRandomReal_of_forall_differentiableAt hz⟩

end AlgorithmicRandomness
