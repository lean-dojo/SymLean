/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import FloatLib.Numerics.Enclosure.Interval.RoundingProof

/-!
# Outward dyadic hulls of rational intervals

`dyadicHull bits I` rounds the lower endpoint of `I` down and the upper endpoint up to the binary
grid of spacing `2 ^ (-bits)`. The result contains `I` (`dyadicHull_sound`), and its endpoint
denominators divide `2 ^ bits`.

## Implementation notes

The rounding is FloatLib's `Interval.dyadicHull`, the interval rounding of
`OutwardRounding.grid bits`, with the order proof of `RationalInterval` attached. FloatLib's
containment theorem `Interval.containsReal_dyadicHull` gives both that order, at the lower
endpoint of `I`, and `dyadicHull_sound`.

We round to a fixed grid to bound the growth of denominators when many enclosures are added or
composed. `dyadicHull_lo` and `dyadicHull_hi` in
`CAS.Continuum.Interval.Rational.DyadicHullEndpoints` give the endpoints as
`⌊I.lo * 2 ^ bits⌋ / 2 ^ bits` and `⌈I.hi * 2 ^ bits⌉ / 2 ^ bits`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>.
* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.3 for the outward rounding (5.14) of the endpoints, there to floating-point numbers.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

/-- Both endpoints of `I` rounded outward to the binary grid of spacing `2 ^ (-bits)`. -/
def dyadicHull (bits : ℕ) (I : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.dyadicHull bits I.toFloatLib)
    (ordered_of_containsReal
      (FloatLib.Numerics.Interval.containsReal_dyadicHull bits I.containsReal_lo))

/-- Every member of `I` is a member of `dyadicHull bits I`. -/
theorem dyadicHull_sound (bits : ℕ) {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : (dyadicHull bits I).MemReal x :=
  ((dyadicHull bits I).toFloatLib_containsReal_iff x).mp
    (FloatLib.Numerics.Interval.containsReal_dyadicHull bits
      ((I.toFloatLib_containsReal_iff x).mpr hx))

end CAS.Continuum.RationalInterval
