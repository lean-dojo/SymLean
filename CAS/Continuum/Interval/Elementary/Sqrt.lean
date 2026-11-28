/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import FloatLib.Numerics.Enclosure.Interval.TotalProof

/-!
# Square-root enclosures from FloatLib

These are FloatLib's enclosures of Mathlib's total square root, `Total.sqrtPoint` and
`Total.sqrt`, with the endpoint order of `RationalInterval` attached. `sqrtPointInterval q steps`
encloses `√q` for every rational `q`. It is `[0, 0]` for negative `q`, where `Real.sqrt` is zero
(`sqrtPointInterval_of_neg`). For `q ≥ 0` it is exact at rational squares and at most
`1 / (q.den * 2 ^ steps)` wide (`sqrtNonnegativePointInterval_width_le`).
`sqrtNonnegativePointInterval` is the same enclosure for a `q` known to be nonnegative.
`sqrtRangeInterval I steps` combines the point enclosures at the two ends of `I`, which is valid
because the square root is monotone, and `sqrtRange` fixes `defaultSqrtRefinementSteps = 12`.
Both contain `Real.sqrt x` for every `x ∈ I`, including the negative members of `I`
(`sqrtRangeInterval_sound`, `sqrtRange_sound`).

## Implementation notes

FloatLib computes and proves the enclosures. For `q ≥ 0`, `Total.sqrtPoint q steps` takes the
integer square-root bounds `sqrtPointBounds` of `q * q.den ^ 2 = q.num * q.den` at `steps`
fractional bits and divides them by `q.den`. The scaled argument is an integer, so its floor loses
nothing, and a square `(a / b) ^ 2` in lowest terms scales to `(a * b) ^ 2`, whose root is found
exactly. Each definition here is one FloatLib call, and each theorem is FloatLib's containment or
width theorem read as `MemReal`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its total square-root
  enclosures and their containment and width theorems.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open FloatLib.Numerics.Interval (Total.sqrtPoint Total.sqrt Total.containsReal_sqrtPoint
  Total.containsReal_sqrt Total.sqrtPoint_def Total.sqrtPoint_width_le)

/-- FloatLib's enclosure of Mathlib's total `Real.sqrt q`, `Total.sqrtPoint q steps`: `[0, 0]`
for negative `q`, and for `q ≥ 0` the integer square-root bounds of `q * q.den ^ 2` at `steps`
fractional bits, divided by `q.den`. -/
def sqrtPointInterval (q : ℚ) (steps : Nat) : RationalInterval :=
  ofFloatLib (Total.sqrtPoint q steps)
    (ordered_of_containsReal (Total.containsReal_sqrtPoint q steps))

/-- `sqrtPointInterval q steps` contains `Real.sqrt q` for every rational `q`. -/
theorem sqrtPointInterval_sound (q : ℚ) (steps : Nat) :
    (sqrtPointInterval q steps).MemReal (Real.sqrt (q : ℝ)) :=
  (memReal_ofFloatLib_iff _ _ _).mpr (Total.containsReal_sqrtPoint q steps)

/-- For negative `q`, `sqrtPointInterval q steps` is `[0, 0]`. -/
theorem sqrtPointInterval_of_neg {q : ℚ} (hq : q < 0) (steps : Nat) :
    sqrtPointInterval q steps = const 0 := by
  have h : Total.sqrtPoint q steps = FloatLib.Numerics.Interval.point 0 := by
    rw [Total.sqrtPoint_def, ite_eq_right (not_le.mpr hq)]
  simp only [sqrtPointInterval, ofFloatLib, const, h]

/-- `sqrtPointInterval q steps` for a `q` known to be nonnegative. -/
def sqrtNonnegativePointInterval (q : ℚ) (_hq : 0 ≤ q) (steps : Nat) : RationalInterval :=
  sqrtPointInterval q steps

/-- `sqrtNonnegativePointInterval q hq steps` contains `Real.sqrt q`. -/
theorem sqrtNonnegativePointInterval_sound (q : ℚ) (hq : 0 ≤ q) (steps : Nat) :
    (sqrtNonnegativePointInterval q hq steps).MemReal (Real.sqrt (q : ℝ)) :=
  sqrtPointInterval_sound q steps

/-- The enclosure of `√q` has width at most `1 / (q.den * 2 ^ steps)`. -/
theorem sqrtNonnegativePointInterval_width_le (q : ℚ) (hq : 0 ≤ q) (steps : Nat) :
    (sqrtNonnegativePointInterval q hq steps).hi -
      (sqrtNonnegativePointInterval q hq steps).lo ≤ 1 / ((q.den : ℚ) * 2 ^ steps) :=
  Total.sqrtPoint_width_le q steps

/-- FloatLib's square-root range of an interval, `Total.sqrt`: the lower point enclosure at
`I.lo` and the upper one at `I.hi`. -/
def sqrtRangeInterval (I : RationalInterval) (steps : Nat) : RationalInterval :=
  ofFloatLib (Total.sqrt I.toFloatLib steps)
    (ordered_of_containsReal (Total.containsReal_sqrt I.toFloatLib steps I.containsReal_lo))

/-- The lower end of `sqrtRangeInterval I steps` is the lower end of the square root at `I.lo`. -/
theorem sqrtRangeInterval_lo (I : RationalInterval) (steps : Nat) :
    (sqrtRangeInterval I steps).lo = (sqrtPointInterval I.lo steps).lo := by
  simp only [sqrtRangeInterval, sqrtPointInterval, Total.sqrt,
    FloatLib.Numerics.Interval.monotoneBounds]
  split <;> rfl

/-- The upper end of `sqrtRangeInterval I steps` is the upper end of the square root at `I.hi`. -/
theorem sqrtRangeInterval_hi (I : RationalInterval) (steps : Nat) :
    (sqrtRangeInterval I steps).hi = (sqrtPointInterval I.hi steps).hi := by
  simp only [sqrtRangeInterval, sqrtPointInterval, Total.sqrt,
    FloatLib.Numerics.Interval.monotoneBounds]
  split
  · next h => exact congrArg (fun q => (Total.sqrtPoint q steps).hi) h
  · rfl

/-- `sqrtRangeInterval I steps` contains `Real.sqrt x` for every `x ∈ I`. -/
theorem sqrtRangeInterval_sound (I : RationalInterval) (steps : Nat)
    {x : ℝ} (hx : I.MemReal x) :
    (sqrtRangeInterval I steps).MemReal (Real.sqrt x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr
    (Total.containsReal_sqrt I.toFloatLib steps ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- Default binary precision on the denominator grid. -/
def defaultSqrtRefinementSteps : Nat := 12

/-- Square-root range at the default precision `defaultSqrtRefinementSteps`. -/
def sqrtRange (I : RationalInterval) : RationalInterval :=
  sqrtRangeInterval I defaultSqrtRefinementSteps

/-- `sqrtRange I` contains `Real.sqrt x` for every `x ∈ I`. -/
theorem sqrtRange_sound (I : RationalInterval) {x : ℝ} (hx : I.MemReal x) :
    (sqrtRange I).MemReal (Real.sqrt x) :=
  sqrtRangeInterval_sound I defaultSqrtRefinementSteps hx

end RationalInterval
end CAS.Continuum
