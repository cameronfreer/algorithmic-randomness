/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Coding.TotalCode
import AlgorithmicRandomness.Randomness.MartinLof

/-!
# Schnorr tests and Schnorr randomness

A Schnorr test is a Martin-Löf test whose canonical increasing stage approximation converges
at a computable rate, witnessed by an actual modulus code: by stage `modulus.apply₂ n k`, the
part of `Uₙ` not yet enumerated has measure at most `2⁻ᵏ`.

Stating the rate against `stageSet` — the canonical approximation from the effective-open layer
— is what makes this a claim about computable convergence rather than an arbitrary set
difference, and it avoids `ENNReal` subtraction entirely.

There is deliberately **no universal Schnorr test of the Martin-Löf enumeration-and-trimming
kind** here, and no generic "randomness notion" abstraction: the computability-of-measure
condition is not effectively certifiable the way the Martin-Löf measure bound can be enforced by
trimming, so any abstraction assuming such a universal test would be wrong for this notion.

Since `SchnorrTest` extends `MartinLofTest`, the capture API is inherited: for `T : SchnorrTest`
the projections `T.openCode`, `T.Captures`, and `T.captureSet` resolve through
`T.toMartinLofTest`, so `MartinLofTest.mem_captureSet` and `MartinLofTest.fairCoin_captureSet`
apply directly and are not restated.
-/

open MeasureTheory
open scoped ENNReal

namespace AlgorithmicRandomness

/-- A Schnorr test: a Martin-Löf test together with a modulus code bounding the measure still
missing from the canonical stage approximation. -/
structure SchnorrTest extends MartinLofTest where
  /-- The modulus: `apply₂ n k` is a stage by which `Uₙ` is approximated to within `2⁻ᵏ`. -/
  modulus : NatFunctionCode
  /-- The uniform tail bound on the canonical increasing stage approximation. -/
  tail_le : ∀ n k, fairCoin (openCode.denote n \ openCode.stageSet n (modulus.apply₂ n k))
    ≤ (2⁻¹ : ℝ≥0∞) ^ k

/-- A point is Schnorr random when no Schnorr test captures it. -/
def IsSchnorrRandom (x : Cantor) : Prop := ∀ T : SchnorrTest, ¬T.Captures x

/-- Martin-Löf randomness implies Schnorr randomness: every Schnorr test is in particular a
Martin-Löf test. -/
theorem IsMartinLofRandom.isSchnorrRandom {x : Cantor} (h : IsMartinLofRandom x) :
    IsSchnorrRandom x := fun T ↦ h T.toMartinLofTest

theorem not_isSchnorrRandom_of_captures {T : SchnorrTest} {x : Cantor} (h : T.Captures x) :
    ¬IsSchnorrRandom x := fun hx ↦ hx T h

end AlgorithmicRandomness
