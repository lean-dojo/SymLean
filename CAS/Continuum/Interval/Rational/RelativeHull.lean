/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DyadicHull

/-!
# Outward rounding to a relative precision

`relativeHull bits I` rounds the endpoints of `I` outward to dyadic rationals with about `bits`
significant bits: each endpoint `q` is replaced by a multiple of `2 ^ (-e)` with
`e = bits - ⌊log₂ |num q|⌋ + ⌊log₂ (den q)⌋`. Unlike the fixed grids of `dyadicHull`, the
precision follows the magnitude of the endpoints.

## Main definitions

* `relativeExponent`: the exponent `e` with `2 ^ (-e)` about `2 ^ (-bits)` times `|q|`.
* `roundDownRel`: `q` rounded down to a multiple of `2 ^ (-relativeExponent bits q)`;
  `roundUpRel` rounds up.
* `relativeHull`: the interval with both endpoints rounded outward to `bits` significant bits.

## Main results

* `roundDownRel_le`: rounding down does not increase `q`.
* `le_roundUpRel`: rounding up does not decrease `q`.
* `relativeHull_sound`: `relativeHull bits I` contains every member of `I`.

## Implementation notes

The rounding is FloatLib's. `relativeHull` is `Interval.relativeHull`, the interval rounding of
`OutwardRounding.relative bits`, with the order proof of `RationalInterval` attached, and
FloatLib's containment theorem gives both that order and the soundness theorem. It holds for
every exponent, so the exponent affects the accuracy and never the soundness.
`relativeExponent` is FloatLib's `Interval.relativeExponent`, which the kernel computes with
`Kernel.log2` in a few steps for a number of any size (`Interval.relativeExponent_eq` states it
with `Nat.log2`). For `q ≠ 0` the product `|q| * 2 ^ e` lies strictly between `2 ^ bits / 2` and
`2 * 2 ^ bits`, so each rounded endpoint is an integer of about `bits` binary digits times a power
of two, whatever the size of `q`.

`roundDownRel` and `roundUpRel` are the formulas `⌊q * 2 ^ e⌋ / 2 ^ e` and `⌈q * 2 ^ e⌉ / 2 ^ e`
with this exponent, written out because proofs unfold them, and `roundDownRel_le` and
`le_roundUpRel` clear the positive power and apply `Int.floor_le` and `Int.le_ceil`. FloatLib's
`Interval.roundDownRel` and `Interval.roundUpRel`, the endpoints of `relativeHull`, have the same
values (`Interval.roundDownRel_eq`, `Interval.roundUpRel_eq`). `IntervalJet.round` in
`CAS.Numerics.IntervalJets` rounds every jet coefficient with `relativeHull`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>.
* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.3 for the outward rounding (5.14) of the endpoints, there to floating-point numbers.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

/-- The exponent `e` with `2 ^ (-e)` about `2 ^ (-bits)` times `|q|`, FloatLib's
`relativeExponent`: `bits - ⌊log₂ |num q|⌋ + ⌊log₂ (den q)⌋`. -/
def relativeExponent (bits : ℕ) (q : ℚ) : ℤ :=
  FloatLib.Numerics.Interval.relativeExponent bits q

/-- `q` rounded down to a multiple of `2 ^ (-relativeExponent bits q)`. -/
def roundDownRel (bits : ℕ) (q : ℚ) : ℚ :=
  (⌊q * 2 ^ relativeExponent bits q⌋ : ℚ) / 2 ^ relativeExponent bits q

/-- `q` rounded up to a multiple of `2 ^ (-relativeExponent bits q)`. -/
def roundUpRel (bits : ℕ) (q : ℚ) : ℚ :=
  (⌈q * 2 ^ relativeExponent bits q⌉ : ℚ) / 2 ^ relativeExponent bits q

/-- Rounding down to `bits` significant bits does not increase `q`. -/
theorem roundDownRel_le (bits : ℕ) (q : ℚ) : roundDownRel bits q ≤ q := by
  unfold roundDownRel
  rw [div_le_iff₀ (zpow_pos (by norm_num) _)]
  exact Int.floor_le _

/-- Rounding up to `bits` significant bits does not decrease `q`. -/
theorem le_roundUpRel (bits : ℕ) (q : ℚ) : q ≤ roundUpRel bits q := by
  unfold roundUpRel
  rw [le_div_iff₀ (zpow_pos (by norm_num) _)]
  exact Int.le_ceil _

/-- The interval with both endpoints rounded outward to `bits` significant bits, FloatLib's
`relativeHull`. -/
def relativeHull (bits : ℕ) (I : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.relativeHull bits I.toFloatLib)
    (ordered_of_containsReal
      (FloatLib.Numerics.Interval.containsReal_relativeHull bits I.containsReal_lo))

/-- `relativeHull bits I` contains every member of `I`. -/
theorem relativeHull_sound (bits : ℕ) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (relativeHull bits I).MemReal x :=
  ((relativeHull bits I).toFloatLib_containsReal_iff x).mp
    (FloatLib.Numerics.Interval.containsReal_relativeHull bits
      ((I.toFloatLib_containsReal_iff x).mpr hx))

end CAS.Continuum.RationalInterval
