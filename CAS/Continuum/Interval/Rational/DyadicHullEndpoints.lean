/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DyadicHull

/-!
# The endpoints of a dyadic hull

The endpoints of `dyadicHull bits I` are the floor and the ceiling of `2 ^ bits` times the
endpoints of `I`, divided by `2 ^ bits` (`dyadicHull_lo`, `dyadicHull_hi`). These are FloatLib's
endpoint equations `Interval.dyadicHull_lo` and `Interval.dyadicHull_hi`, which rest on the floor
and the ceiling form of its grid enclosure (`BinaryGrid.enclose_lo_eq_floor`,
`BinaryGrid.enclose_hi_eq_ceil`).

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

/-- The lower endpoint of `dyadicHull bits I` is `⌊I.lo 2 ^ bits⌋ / 2 ^ bits`. -/
theorem dyadicHull_lo (bits : ℕ) (I : RationalInterval) :
    (dyadicHull bits I).lo = (⌊I.lo * 2 ^ bits⌋ : ℚ) / 2 ^ bits :=
  FloatLib.Numerics.Interval.dyadicHull_lo bits I.toFloatLib

/-- The upper endpoint of `dyadicHull bits I` is `⌈I.hi 2 ^ bits⌉ / 2 ^ bits`. -/
theorem dyadicHull_hi (bits : ℕ) (I : RationalInterval) :
    (dyadicHull bits I).hi = (⌈I.hi * 2 ^ bits⌉ : ℚ) / 2 ^ bits :=
  FloatLib.Numerics.Interval.dyadicHull_hi bits I.toFloatLib

end CAS.Continuum.RationalInterval
