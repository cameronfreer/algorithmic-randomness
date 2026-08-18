/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Complexity.Incompressible
import AlgorithmicRandomness.Complexity.TestRequests

/-!
# The Levin–Schnorr theorem

A point of Cantor space is Martin-Löf random exactly when its initial segments are incompressible:

```text
IsMartinLofRandom x  ↔  ∃ c, ∀ n, n ≤ prefixComplexity (initSeg x n) + c
```

The statement is subtraction-free. Writing it as `n - c ≤ K(x ↾ n)` would introduce truncated
natural subtraction and make the small-`n` cases vacuous for the wrong reason.

The two directions come from opposite constructions. Forward is the compression test: the strings
with `K(τ) + c < |τ|` form a Martin-Löf test whose measure the *finite* Kraft inequality bounds,
so a random point escapes at some level, and that level is the constant. Backward is Kraft–Chaitin
allocation: a test capturing `x` is turned into a request stream, the requests are realized by an
actual prefix-free machine, and optimality of the universal machine absorbs the difference.

The constant in the backward direction is absorbed through
`prefixComplexity_le_add_of_describes` rather than `prefixComplexity_le_length`, because the
machine built from the requests is *not* the universal machine — it is some prefix-free machine,
and what relates it to prefix complexity is optimality.
-/

namespace AlgorithmicRandomness

/-! ## Unbounded deficiency along a captured point -/

/-- **Gate 7.** A point captured by a test has initial segments of unbounded compression
deficiency. -/
theorem MartinLofTest.unbounded_deficiency_of_captures (T : MartinLofTest) {x : Cantor}
    (hx : T.Captures x) : ∀ c, ∃ m, prefixComplexity (initSeg x m) + c < m := by
  obtain ⟨d, hd⟩ := prefixComplexity_le_add_of_describes T.kraftRequestTrace.machine
  intro c
  obtain ⟨r, ⟨R, hrR⟩, hxr, hlen⟩ :=
    exists_request_of_mem_denote_add T (hx (2 * (c + d + 1) + 1))
  obtain ⟨p, hplen, hpd⟩ := T.kraftRequestTrace.request_described hrR
  have hK : prefixComplexity r.output ≤ p.length + d := hd hpd
  rw [hplen] at hK
  refine ⟨r.output.length, ?_⟩
  rw [initSeg_of_mem_cylinder hxr]
  omega

theorem prefixComplexity_unbounded_of_not_isMartinLofRandom {x : Cantor}
    (hx : ¬IsMartinLofRandom x) : ∀ c, ∃ m, prefixComplexity (initSeg x m) + c < m := by
  rw [IsMartinLofRandom, not_forall] at hx
  obtain ⟨T, hT⟩ := hx
  exact T.unbounded_deficiency_of_captures (not_not.mp hT)

/-! ## The theorem -/

/-- **Levin–Schnorr.** Martin-Löf randomness is incompressibility of initial segments. -/
theorem isMartinLofRandom_iff_prefixComplexity {x : Cantor} :
    IsMartinLofRandom x ↔ ∃ c, ∀ n, n ≤ prefixComplexity (initSeg x n) + c := by
  refine ⟨IsMartinLofRandom.prefixComplexity_lowerBound, fun ⟨c, hc⟩ ↦ ?_⟩
  by_contra hx
  obtain ⟨m, hm⟩ := prefixComplexity_unbounded_of_not_isMartinLofRandom hx c
  exact absurd (hc m) (by omega)

end AlgorithmicRandomness
