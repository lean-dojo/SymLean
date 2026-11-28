/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic -- shake: keep: re-exported for PDEAtlas
public import FloatLib.Numerics.Enclosure.Interval.SharpTrigProof

/-!
# Sine and cosine enclosures from FloatLib

These are FloatLib's sine and cosine enclosures of `FloatLib.Numerics.Interval.SharpTrig` at
Taylor degree `32` on the binary grid of step `2 ^ (-128)`, with the endpoint order of
`RationalInterval` attached.

`sinBase` and `cosBase` are FloatLib's midpoint enclosures (period reduction and the Lipschitz
bound), rounded outward to the grid, and `sinPoint` and `cosPoint` are the same enclosures at a
rational point. `sin` and `cos` are FloatLib's sharp enclosures `sharpSinBounds` and
`sharpCosBounds`. They intersect the base enclosure with the point enclosures at the two ends of
the interval where these bound the range: on `[-π/2, π/2]` and `[0, π]` for sine, on `[0, π]`,
`[-π, 0]` and an interval of `[-π, π]` around zero for cosine, and wherever the enclosure of the
derivative has one sign. On `[0, π]` the sine enclosure is raised to zero from below, and so is the
cosine enclosure on `[-π/2, π/2]`. The branch tests are exact rational comparisons of the ends of
the interval with `piLower`, Mathlib's twenty-decimal lower bound of `π`.

## Main definitions

* `sinBase`, `cosBase`, `sinPoint`, `cosPoint`: the midpoint enclosures, on an interval and at a
  point.
* `RationalInterval.sin`, `RationalInterval.cos`: the sharp enclosures.

## Main results

* `sinBase_sound`, `cosBase_sound`, `sin_sound`, `cos_sound`: each enclosure of an interval `I`
  contains the sine or the cosine of every `x ∈ I`.
* `sinPoint_sound`, `cosPoint_sound`: the point enclosures contain `Real.sin q` and `Real.cos q`.

## Implementation notes

Each definition is one FloatLib call. Its order proof is FloatLib's containment theorem at the
lower endpoint of `I` (`ordered_of_containsReal`), and each `_sound` theorem is FloatLib's
containment theorem read as `MemReal`. FloatLib states the definitions in ordinary notation
(`sharpSinBounds_def`, `sinMonotoneBase_def` and the others) and proves the monotonicity bounds
with Mathlib's monotonicity of sine on `[-π/2, π/2]` and of cosine on `[0, π]`. The module still
exports the interval arithmetic of `CAS.Continuum.Interval.Rational.Arithmetic`, which PDEAtlas
combines with `sinPoint` and `cosPoint`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its sharp sine and
  cosine enclosures and their containment theorems.
* NIST Digital Library of Mathematical Functions, §4.19 Maclaurin Series and Laurent Series,
  Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/4.19>. Equations (4.19.1) and (4.19.2), the
  series of `sin z` and `cos z` that FloatLib sums.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open FloatLib.Numerics.Interval (containsReal_sinBase containsReal_cosBase sharpSinBounds
  sharpCosBounds containsReal_sharpSinBounds containsReal_sharpCosBounds)

/-- FloatLib's midpoint enclosure of `Real.sin` on `I` at Taylor degree `32`, rounded outward to
the grid of step `2 ^ (-128)`. -/
def sinBase (I : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.sinBase I.toFloatLib 32 128)
    (ordered_of_containsReal (containsReal_sinBase I.toFloatLib 32 128 I.containsReal_lo))

/-- `sinBase I` contains `Real.sin x` for every `x ∈ I`. -/
theorem sinBase_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (sinBase I).MemReal (Real.sin x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr
    (containsReal_sinBase I.toFloatLib 32 128 ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- FloatLib's enclosure of `Real.sin q` at a rational point, `sinBase` of `[q, q]`. -/
def sinPoint (q : ℚ) : RationalInterval := sinBase (const q)

/-- `sinPoint q` contains `Real.sin q`. -/
theorem sinPoint_sound (q : ℚ) : (sinPoint q).MemReal (Real.sin (q : ℝ)) :=
  sinBase_sound (memReal_const q)

/-- FloatLib's midpoint enclosure of `Real.cos` on `I` at Taylor degree `32`, rounded outward to
the grid of step `2 ^ (-128)`. -/
def cosBase (I : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.cosBase I.toFloatLib 32 128)
    (ordered_of_containsReal (containsReal_cosBase I.toFloatLib 32 128 I.containsReal_lo))

/-- `cosBase I` contains `Real.cos x` for every `x ∈ I`. -/
theorem cosBase_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (cosBase I).MemReal (Real.cos x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr
    (containsReal_cosBase I.toFloatLib 32 128 ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- FloatLib's enclosure of `Real.cos q` at a rational point, `cosBase` of `[q, q]`. -/
def cosPoint (q : ℚ) : RationalInterval := cosBase (const q)

/-- `cosPoint q` contains `Real.cos q`. -/
theorem cosPoint_sound (q : ℚ) : (cosPoint q).MemReal (Real.cos (q : ℝ)) :=
  cosBase_sound (memReal_const q)

/--
The sine enclosure of a rational interval: FloatLib's `sharpSinBounds` at Taylor degree `32` on
the grid of step `2 ^ (-128)`, that is `sinBase I` narrowed by the point enclosures at the ends of
`I` where these bound the range, and raised to zero from below on `[0, π]`.
-/
def sin (I : RationalInterval) : RationalInterval :=
  ofFloatLib (sharpSinBounds I.toFloatLib 32 128)
    (ordered_of_containsReal (containsReal_sharpSinBounds I.toFloatLib 32 128 I.containsReal_lo))

/-- `I.sin` contains `Real.sin x` for every `x ∈ I`. -/
theorem sin_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    I.sin.MemReal (Real.sin x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr
    (containsReal_sharpSinBounds I.toFloatLib 32 128 ((I.toFloatLib_containsReal_iff x).mpr hx))

/--
The cosine enclosure of a rational interval: FloatLib's `sharpCosBounds` at Taylor degree `32` on
the grid of step `2 ^ (-128)`, that is `cosBase I` narrowed by the point enclosures at the ends of
`I` where these bound the range, and raised to zero from below on `[-π/2, π/2]`.
-/
def cos (I : RationalInterval) : RationalInterval :=
  ofFloatLib (sharpCosBounds I.toFloatLib 32 128)
    (ordered_of_containsReal (containsReal_sharpCosBounds I.toFloatLib 32 128 I.containsReal_lo))

/-- `I.cos` contains `Real.cos x` for every `x ∈ I`. -/
theorem cos_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    I.cos.MemReal (Real.cos x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr
    (containsReal_sharpCosBounds I.toFloatLib 32 128 ((I.toFloatLib_containsReal_iff x).mpr hx))

end RationalInterval
end CAS.Continuum
