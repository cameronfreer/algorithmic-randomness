/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness.Analysis.AffineDyadic
import AlgorithmicRandomness.Analysis.ComputableMonotone
import AlgorithmicRandomness.Martingale.Simulate

/-!
# The slope martingale of a monotone function on an affine grid

The chord slope of a nondecreasing function across the cells of a rationally scaled and shifted
dyadic grid is a martingale: fairness is the averaging identity `slope_children_add`, and
nonnegativity is monotonicity. That much is free.

The work is the *error coding*. The capital is a real number, so it is presented as an
`ApproximableTreeMartingale` and handed to the existing bounded-error simulation, which returns an
exact-rational `ComputableMartingale`. Three things have to be arranged for that.

*The division is exact.* Both endpoints are approximated to a common precision and their difference
is divided by the cell width, which is an exact positive coded rational — so only the endpoint
error propagates, scaled by the reciprocal width.

*The precision is searched for, not computed.* The required endpoint precision depends on the
width, which varies with the string; the search is a comparison of coded rationals, stated
multiplicatively so that no division enters the executable test, and terminates because the width
is positive.

*The sign is arranged, not assumed.* The approximation is signed, and `RatCode.toNNRat` may only be
used with an explicit sign proof. Adding the exact margin `2⁻⁽ⁱ⁺¹⁾` before the conversion makes the
result provably nonnegative — the true slope is — while keeping it within `2⁻ⁱ`.
-/

open scoped NNRat NNReal

namespace AlgorithmicRandomness

variable (g : ComputableMonotone) (G : AffineDyadicGrid)

/-! ## The real martingale -/

/-- The chord slope across the affine cell named by `σ`, as a nonnegative real. -/
noncomputable def affineSlope (σ : BitString) : ℝ≥0 :=
  ⟨slope g.toFun (G.left σ) (G.right σ), G.slope_nonneg_of_monotone g.monotone_toFun σ⟩

@[simp] theorem coe_affineSlope (σ : BitString) :
    ((affineSlope g G σ : ℝ≥0) : ℝ) = slope g.toFun (G.left σ) (G.right σ) := rfl

/-- **The slope martingale.** Fairness is the averaging identity of the two children. -/
noncomputable def affineSlopeMartingale : RealTreeMartingale where
  capital := affineSlope g G
  fair σ := by
    refine NNReal.eq ?_
    push_cast
    exact G.slope_children_add g.toFun σ

@[simp] theorem affineSlopeMartingale_capital (σ : BitString) :
    (affineSlopeMartingale g G).capital σ = affineSlope g G σ := rfl

/-! ## The width as a nonnegative code -/

/-- The cell width, in the nonnegative layer. The sign proof is the width's positivity. -/
def widthNNCode (σ : BitString) : ℕ := RatCode.toNNRat (G.widthCode σ)

theorem coe_value_widthNNCode (σ : BitString) :
    ((NNRatCode.value (widthNNCode G σ) : ℚ≥0) : ℝ) = G.width σ := by
  have hpos : (0 : ℚ) ≤ RatCode.value (G.widthCode σ) := by
    have h := G.value_widthCode σ
    have hw := (G.width_pos σ).le
    rw [← h] at hw
    exact_mod_cast hw
  have h : ((NNRatCode.value (widthNNCode G σ) : ℚ≥0) : ℚ) = RatCode.value (G.widthCode σ) :=
    RatCode.value_toNNRat hpos
  rw [← G.value_widthCode σ, ← h]
  push_cast
  ring

theorem value_widthNNCode_pos (σ : BitString) : 0 < NNRatCode.value (widthNNCode G σ) := by
  have h := coe_value_widthNNCode G σ
  have hpos := G.width_pos σ
  rw [← h] at hpos
  exact_mod_cast hpos

/-! ## The signed slope approximation -/

/-- Approximate both endpoint values to precision `t`, subtract, and divide by the exact width. -/
def slopeApproxCode (σ : BitString) (t : ℕ) : ℕ :=
  RatCode.divNNRat
    (RatCode.sub (g.approxAtCode (G.rightCode σ) t) (g.approxAtCode (G.leftCode σ) t))
    (widthNNCode G σ)

theorem slopeApprox_error (σ : BitString) (t : ℕ) :
    |((RatCode.value (slopeApproxCode g G σ t) : ℚ) : ℝ)
        - ((affineSlope g G σ : ℝ≥0) : ℝ)|
      ≤ 2 * (2⁻¹ : ℝ) ^ t / G.width σ := by
  have hw : (0 : ℝ) < G.width σ := G.width_pos σ
  have hleft := g.abs_toFun_sub_approxAt_le (G.leftCode σ) t
  have hright := g.abs_toFun_sub_approxAt_le (G.rightCode σ) t
  rw [G.value_leftCode σ] at hleft
  rw [G.value_rightCode σ] at hright
  have hvalue : ((RatCode.value (slopeApproxCode g G σ t) : ℚ) : ℝ)
      = (((g.approxAt (G.rightCode σ) t : ℚ) : ℝ) - ((g.approxAt (G.leftCode σ) t : ℚ) : ℝ))
        / G.width σ := by
    rw [slopeApproxCode, RatCode.value_divNNRat (value_widthNNCode_pos G σ), RatCode.value_sub]
    push_cast
    rw [coe_value_widthNNCode G σ]
    rfl
  have hslope : ((affineSlope g G σ : ℝ≥0) : ℝ)
      = (g.toFun (G.right σ) - g.toFun (G.left σ)) / G.width σ := by
    rw [coe_affineSlope, slope_def_field, AffineDyadicGrid.right]
    ring_nf
  rw [hvalue, hslope, div_sub_div_same, abs_div, abs_of_pos hw, div_le_div_iff_of_pos_right hw]
  calc |((g.approxAt (G.rightCode σ) t : ℚ) : ℝ) - ((g.approxAt (G.leftCode σ) t : ℚ) : ℝ)
          - (g.toFun (G.right σ) - g.toFun (G.left σ))|
      = |(((g.approxAt (G.rightCode σ) t : ℚ) : ℝ) - g.toFun (G.right σ))
          - (((g.approxAt (G.leftCode σ) t : ℚ) : ℝ) - g.toFun (G.left σ))| := by
        congr 1
        ring
    _ ≤ |((g.approxAt (G.rightCode σ) t : ℚ) : ℝ) - g.toFun (G.right σ)|
        + |((g.approxAt (G.leftCode σ) t : ℚ) : ℝ) - g.toFun (G.left σ)| := abs_sub _ _
    _ = |g.toFun (G.right σ) - ((g.approxAt (G.rightCode σ) t : ℚ) : ℝ)|
        + |g.toFun (G.left σ) - ((g.approxAt (G.leftCode σ) t : ℚ) : ℝ)| := by
        rw [abs_sub_comm (((g.approxAt (G.rightCode σ) t : ℚ) : ℝ)),
          abs_sub_comm (((g.approxAt (G.leftCode σ) t : ℚ) : ℝ))]
    _ ≤ (2⁻¹ : ℝ) ^ t + (2⁻¹ : ℝ) ^ t := add_le_add hright hleft
    _ = 2 * (2⁻¹ : ℝ) ^ t := by ring

/-! ## The precision search

The endpoint precision needed depends on the cell width, so it is searched for. The test is stated
multiplicatively — `2 · 2⁻ᵗ ≤ 2⁻⁽ⁱ⁺¹⁾ · width` — so the executable comparison never divides. -/

/-- The string named by the first component of a paired input. -/
private def decodeString (m : ℕ) : BitString := (Encodable.decode (α := BitString) m).getD []

@[simp] private theorem decodeString_encode (σ : BitString) :
    decodeString (Encodable.encode σ) = σ := by
  rw [decodeString, Encodable.encodek, Option.getD_some]

private theorem primrec_decodeString : Primrec decodeString :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem primrec_widthNNCode : Primrec (widthNNCode G) :=
  RatCode.primrec_toNNRat.comp G.primrec_widthCode

/-- The precision test. -/
def fineT (σ : BitString) (i t : ℕ) : Bool :=
  NNRatCode.le (NNRatCode.divPowTwo t (NNRatCode.ofNat 2))
    (NNRatCode.mul (NNRatCode.divPowTwo (i + 1) (NNRatCode.ofNat 1)) (widthNNCode G σ))

theorem fineT_iff {σ : BitString} {i t : ℕ} :
    fineT G σ i t = true ↔ 2 * (2⁻¹ : ℝ) ^ t ≤ (2⁻¹ : ℝ) ^ (i + 1) * G.width σ := by
  rw [fineT, NNRatCode.le_iff, NNRatCode.value_mul, NNRatCode.value_divPowTwo,
    NNRatCode.value_divPowTwo, NNRatCode.value_ofNat, NNRatCode.value_ofNat]
  rw [← NNRat.cast_le (K := ℝ)]
  push_cast
  rw [coe_value_widthNNCode G σ, inv_pow, inv_pow]
  constructor
  · intro h
    calc 2 * (2 ^ t : ℝ)⁻¹ = 2 / 2 ^ t := by ring
      _ ≤ 1 / 2 ^ (i + 1) * G.width σ := h
      _ = (2 ^ (i + 1) : ℝ)⁻¹ * G.width σ := by ring
  · intro h
    calc (2 : ℝ) / 2 ^ t = 2 * (2 ^ t : ℝ)⁻¹ := by ring
      _ ≤ (2 ^ (i + 1) : ℝ)⁻¹ * G.width σ := h
      _ = 1 / 2 ^ (i + 1) * G.width σ := by ring

theorem exists_fineT (σ : BitString) (i : ℕ) : ∃ t, fineT G σ i t = true := by
  have hpos : (0 : ℝ) < (2⁻¹ : ℝ) ^ (i + 1) * G.width σ := by
    have := G.width_pos σ
    positivity
  have htend : Filter.Tendsto (fun t : ℕ ↦ 2 * (2⁻¹ : ℝ) ^ t) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)
    simpa using h.const_mul (2 : ℝ)
  obtain ⟨t, ht⟩ := (htend.eventually (gt_mem_nhds hpos)).exists
  exact ⟨t, (fineT_iff G).mpr ht.le⟩

private theorem primrec_fineT : Primrec fun w : (ℕ × ℕ) × ℕ ↦
    fineT G (decodeString w.1.1) w.1.2 w.2 := by
  have hleft : Primrec fun w : (ℕ × ℕ) × ℕ ↦ NNRatCode.divPowTwo w.2 (NNRatCode.ofNat 2) :=
    NNRatCode.primrec_divPowTwo.comp Primrec.snd (Primrec.const _)
  have hright : Primrec fun w : (ℕ × ℕ) × ℕ ↦
      NNRatCode.mul (NNRatCode.divPowTwo (w.1.2 + 1) (NNRatCode.ofNat 1))
        (widthNNCode G (decodeString w.1.1)) :=
    NNRatCode.primrec_mul.comp
      (NNRatCode.primrec_divPowTwo.comp
        (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const _))
      ((primrec_widthNNCode G).comp (primrec_decodeString.comp (Primrec.fst.comp Primrec.fst)))
  exact NNRatCode.primrec_le.comp hleft hright

/-- The search for a fine enough endpoint precision, on paired input `⟨encode σ, i⟩`. -/
noncomputable def precisionSearch (w : ℕ) : Part ℕ :=
  Nat.rfind fun t ↦ Part.some (fineT G (decodeString w.unpair.1) w.unpair.2 t)

theorem partrec_precisionSearch : Nat.Partrec fun w ↦ precisionSearch G w := by
  have hin : Computable fun p : ℕ × ℕ ↦ (p.1.unpair, p.2) :=
    Computable.pair (Primrec.unpair.comp Primrec.fst).to_comp Computable.snd
  have h : Computable fun p : ℕ × ℕ ↦
      fineT G (decodeString p.1.unpair.1) p.1.unpair.2 p.2 :=
    ((primrec_fineT G).to_comp.comp hin).of_eq fun _ ↦ rfl
  exact Partrec.nat_iff.mp (Partrec.rfind (Computable₂.partrec₂ h.to₂))

theorem precisionSearch_dom (w : ℕ) : (precisionSearch G w).Dom := by
  obtain ⟨t, ht⟩ := exists_fineT G (decodeString w.unpair.1) w.unpair.2
  obtain ⟨m, hm, -⟩ := Nat.rfind_min'
    (p := fun t ↦ fineT G (decodeString w.unpair.1) w.unpair.2 t) ht
  exact Part.dom_iff_mem.mpr ⟨m, hm⟩

/-- The bundled precision program. -/
noncomputable def precisionCode : NatFunctionCode :=
  NatFunctionCode.ofPartrecTotal (partrec_precisionSearch G) (precisionSearch_dom G)

/-- The selected precision. -/
noncomputable def precision (w : ℕ) : ℕ := (precisionCode G).toFun w

theorem computable_precision : Computable (precision G) := (precisionCode G).computable_toFun

theorem fineT_precision (w : ℕ) :
    fineT G (decodeString w.unpair.1) w.unpair.2 (precision G w) = true := by
  have hmem : precision G w ∈ precisionSearch G w := by
    rw [precision, precisionCode, NatFunctionCode.ofPartrecTotal_toFun]
    exact Part.get_mem _
  simpa using Nat.rfind_spec hmem

/-! ## The approximation program -/

/-- On `⟨encode σ, i⟩`: the signed slope approximation at the selected precision, shifted up by the
exact margin `2⁻⁽ⁱ⁺¹⁾` so that the conversion to the nonnegative layer has its sign proof. -/
noncomputable def slopeApproxFun (w : ℕ) : ℕ :=
  RatCode.toNNRat (RatCode.add
    (slopeApproxCode g G (decodeString w.unpair.1) (precision G w))
    (RatCode.ofNNRat (NNRatCode.divPowTwo (w.unpair.2 + 1) (NNRatCode.ofNat 1))))

-- The precision program is an extracted `Classical.choose` term; sealing it keeps the
-- computability proof below from unfolding into it. The intermediate steps are also left
-- unannotated: stating their types would make each `.comp` unify against the full term.
attribute [local irreducible] precisionCode precision

theorem computable_slopeApproxFun : Computable (slopeApproxFun g G) := by
  have hstr : Computable fun w : ℕ ↦ decodeString w.unpair.1 :=
    (primrec_decodeString.comp (Primrec.fst.comp Primrec.unpair)).to_comp
  have hprec : Computable fun w : ℕ ↦ precision G w := computable_precision G
  have hR := Computable₂.comp g.computable_approxAtCode
    (G.primrec_rightCode.to_comp.comp hstr) hprec
  have hL := Computable₂.comp g.computable_approxAtCode
    (G.primrec_leftCode.to_comp.comp hstr) hprec
  have hdiff := Computable₂.comp RatCode.primrec_sub.to_comp hR hL
  have hslope := Computable₂.comp RatCode.primrec_divNNRat.to_comp hdiff
    ((primrec_widthNNCode G).to_comp.comp hstr)
  have hmargin : Computable fun w : ℕ ↦
      RatCode.ofNNRat (NNRatCode.divPowTwo (w.unpair.2 + 1) (NNRatCode.ofNat 1)) :=
    (RatCode.primrec_ofNNRat.comp
      (NNRatCode.primrec_divPowTwo.comp
        (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const _))).to_comp
  have hsum := Computable₂.comp RatCode.primrec_add.to_comp hslope hmargin
  exact (RatCode.primrec_toNNRat.to_comp.comp hsum).of_eq fun _ ↦ rfl

/-! ## The approximation guarantee and the bundle -/

theorem slopeApprox_spec (σ : BitString) (i : ℕ) :
    |((NNRatCode.value (slopeApproxFun g G (Nat.pair (Encodable.encode σ) i)) : ℚ≥0) : ℝ)
      - ((affineSlope g G σ : ℝ≥0) : ℝ)| ≤ (2 : ℝ)⁻¹ ^ i := by
  have hdec : decodeString (Nat.pair (Encodable.encode σ) i).unpair.1 = σ := by
    rw [Nat.unpair_pair, decodeString_encode]
  have hi : (Nat.pair (Encodable.encode σ) i).unpair.2 = i := by rw [Nat.unpair_pair]
  set t := precision G (Nat.pair (Encodable.encode σ) i) with ht
  have hfine := fineT_precision G (Nat.pair (Encodable.encode σ) i)
  rw [hdec, hi, ← ht] at hfine
  have hfineR := (fineT_iff G).mp hfine
  have hwpos : (0 : ℝ) < G.width σ := G.width_pos σ
  have herr : |((RatCode.value (slopeApproxCode g G σ t) : ℚ) : ℝ)
      - ((affineSlope g G σ : ℝ≥0) : ℝ)| ≤ (2⁻¹ : ℝ) ^ (i + 1) := by
    refine le_trans (slopeApprox_error g G σ t) ?_
    rw [div_le_iff₀ hwpos]
    linarith
  set margin : ℕ := RatCode.ofNNRat (NNRatCode.divPowTwo (i + 1) (NNRatCode.ofNat 1)) with hmargin
  have hmarginval : ((RatCode.value margin : ℚ) : ℝ) = (2⁻¹ : ℝ) ^ (i + 1) := by
    rw [hmargin, RatCode.value_ofNNRat, NNRatCode.value_divPowTwo, NNRatCode.value_ofNat]
    push_cast
    rw [inv_pow]
    ring
  set S : ℕ := RatCode.add (slopeApproxCode g G σ t) margin with hS
  have hSval : ((RatCode.value S : ℚ) : ℝ)
      = ((RatCode.value (slopeApproxCode g G σ t) : ℚ) : ℝ) + (2⁻¹ : ℝ) ^ (i + 1) := by
    rw [hS, RatCode.value_add, ← hmarginval]
    push_cast
    ring
  have hnonneg : (0 : ℚ) ≤ RatCode.value S := by
    have h1 : ((affineSlope g G σ : ℝ≥0) : ℝ) ≤ ((RatCode.value S : ℚ) : ℝ) := by
      rw [hSval]
      have h := abs_le.mp herr
      linarith [h.1]
    have h2 : (0 : ℝ) ≤ ((RatCode.value S : ℚ) : ℝ) :=
      le_trans (affineSlope g G σ).coe_nonneg h1
    exact_mod_cast h2
  have hfin : ((NNRatCode.value (slopeApproxFun g G (Nat.pair (Encodable.encode σ) i)) : ℚ≥0) : ℝ)
      = ((RatCode.value S : ℚ) : ℝ) := by
    rw [slopeApproxFun, hdec, hi, ← ht, ← hmargin, ← hS]
    rw [← RatCode.value_toNNRat hnonneg]
    push_cast
    ring
  rw [hfin, hSval]
  have h := abs_le.mp herr
  have hm2 : (2⁻¹ : ℝ) ^ (i + 1) + (2⁻¹ : ℝ) ^ (i + 1) = (2 : ℝ)⁻¹ ^ i := by
    rw [pow_succ]
    ring
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- **The approximable slope martingale.** -/
noncomputable def affineSlopeApproximable : ApproximableTreeMartingale where
  toRealTreeMartingale := affineSlopeMartingale g G
  approxCode := NatFunctionCode.ofComputable (computable_slopeApproxFun g G)
  approx_spec σ i := by
    rw [NatFunctionCode.apply₂, NatFunctionCode.ofComputable_toFun]
    exact slopeApprox_spec g G σ i

/-- The exact-rational martingale obtained from it by the bounded-error simulation. -/
noncomputable def affineSlopeComputable : ComputableMartingale :=
  (affineSlopeApproximable g G).simulate

/-- **Pointwise domination.** The simulation is never below the slope, which is what carries
unbounded slopes to success. -/
theorem affineSlope_le_affineSlopeComputable (σ : BitString) :
    ((affineSlope g G σ : ℝ≥0) : ℝ)
      ≤ (((affineSlopeComputable g G).capital σ : ℚ≥0) : ℝ) :=
  (affineSlopeApproximable g G).simulate_ge σ

/-! ## The bounded form

What the geometry downstream consumes is not success but its contrapositive: along a computably
random point the chord slopes over the grid's cells are bounded. -/

private theorem succeeds_of_unbounded_affineSlope {x : Cantor}
    (h : ∀ C : ℝ, ∃ n, C < slope g.toFun (G.left (initSeg x n)) (G.right (initSeg x n))) :
    (affineSlopeComputable g G).Succeeds x := by
  intro c
  obtain ⟨n, hn⟩ := h ((c : ℚ≥0) : ℝ)
  refine ⟨n, ?_⟩
  have hdom := affineSlope_le_affineSlopeComputable g G (initSeg x n)
  rw [coe_affineSlope] at hdom
  have : ((c : ℚ≥0) : ℝ) ≤ (((affineSlopeComputable g G).capital (initSeg x n) : ℚ≥0) : ℝ) := by
    linarith
  exact_mod_cast this

/-- **Bounded slopes along a computably random point.** -/
theorem IsComputablyRandom.affineSlope_bounded {x : Cantor} (hx : IsComputablyRandom x)
    (g : ComputableMonotone) (G : AffineDyadicGrid) :
    ∃ C : ℝ, ∀ n, slope g.toFun (G.left (initSeg x n)) (G.right (initSeg x n)) ≤ C := by
  by_contra hcon
  have h : ∀ C : ℝ, ∃ n, C < slope g.toFun (G.left (initSeg x n)) (G.right (initSeg x n)) := by
    intro C
    by_contra hC
    exact hcon ⟨C, fun n ↦ not_lt.mp fun hlt ↦ hC ⟨n, hlt⟩⟩
  exact hx (affineSlopeComputable g G) (succeeds_of_unbounded_affineSlope g G h)

end AlgorithmicRandomness
