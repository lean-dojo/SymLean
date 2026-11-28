/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic

/-!
# Inflation and intersection of rational intervals

Two operations on rational intervals: `inflate` widens an interval by a radius, and `intersect`
sharpens an enclosure with a second one.

* `inflate I r hr` is `[I.lo - r, I.hi + r]` for `hr : 0 ≤ r`; by `inflate_sound` it contains
  every `value` with `|value - center| ≤ r` for some `center ∈ I`;
* `intersect I J h` is the intersection of `I` and `J` given a proof `h` that it is nonempty,
  FloatLib's `Interval.Exact.intersect`; by `intersect_sound` it contains every common member of
  `I` and `J`.

## Implementation notes

Both operations are executable; their proof arguments only establish the endpoint order and are
erased at run time. `inflate` subtracts and adds `r` in `ℚ`, and `inflate_sound` splits the
hypothesis with `abs_le` and closes both sides by `linarith`. The ball version
`IntervalBalls.inflate` of `CAS.Numerics.IntervalBalls` reads the endpoints `I.lo - r` and
`I.hi + r` from this definition (`IntervalBalls.inflate_encloses`). `intersect` is FloatLib's
total intersection, which still compares `max I.lo J.lo` with `min I.hi J.hi` when it runs and
returns `I` for disjoint inputs. Under `hoverlap` it is `[max I.lo J.lo, min I.hi J.hi]`
(`Interval.Exact.intersect_eq_of_le`), which gives the endpoint order, `intersect_lo` and
`intersect_hi`, and FloatLib's `Interval.Exact.containsReal_intersect` gives `intersect_sound`.
`meet` of `CAS.Continuum.Interval.Rational.Meet` is the same intersection without the overlap
proof.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open FloatLib.Numerics.Interval

/-- Inflate both sides of an interval by a nonnegative rational radius. -/
def inflate (I : RationalInterval) (r : ℚ) (hr : 0 ≤ r) : RationalInterval where
  lo := I.lo - r
  hi := I.hi + r
  hle := by
    linarith [I.hle]

/-- If `center ∈ I` and `|value - center| ≤ r`, then `value ∈ I.inflate r hr`. -/
theorem inflate_sound {I : RationalInterval} {r : ℚ} (hr : 0 ≤ r)
    {center value : ℝ} (hcenter : I.MemReal center)
    (herror : |value - center| ≤ (r : ℝ)) :
    (I.inflate r hr).MemReal value := by
  obtain ⟨h1, h2⟩ := abs_le.mp herror
  push_cast [MemReal, inflate]
  constructor <;> linarith [hcenter.1, hcenter.2]

/--
The intersection `[max I.lo J.lo, min I.hi J.hi]` of two rational intervals, given that it is
nonempty.

FloatLib computes the endpoints, and the overlap hypothesis, an exact rational inequality, is
their order.
-/
def intersect (I J : RationalInterval)
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi) : RationalInterval :=
  ofFloatLib (Exact.intersect I.toFloatLib J.toFloatLib) (by
    rw [Exact.intersect_lo, Exact.intersect_hi]
    exact hoverlap)

/-- FloatLib's intersection selects the larger lower endpoint. -/
@[simp] theorem intersect_lo (I J : RationalInterval)
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi) :
    (I.intersect J hoverlap).lo = max I.lo J.lo :=
  Exact.intersect_lo _ _

/-- FloatLib's intersection selects the smaller upper endpoint. -/
@[simp] theorem intersect_hi (I J : RationalInterval)
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi) :
    (I.intersect J hoverlap).hi = min I.hi J.hi :=
  Exact.intersect_hi _ _

/-- Membership in both input intervals gives membership in their intersection. -/
theorem intersect_sound {I J : RationalInterval}
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi)
    {x : ℝ} (hI : I.MemReal x) (hJ : J.MemReal x) :
    (I.intersect J hoverlap).MemReal x :=
  ((I.intersect J hoverlap).toFloatLib_containsReal_iff x).mp (Exact.containsReal_intersect
    ((I.toFloatLib_containsReal_iff x).mpr hI) ((J.toFloatLib_containsReal_iff x).mpr hJ))

end RationalInterval
end CAS.Continuum
