/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic

/-!
# The meet of two rational intervals

When a real number is enclosed by two intervals computed in different ways, it lies in their
intersection. `RationalInterval.meet I J` is that intersection when its endpoints are ordered,
and `I` otherwise; in both cases it contains every common member (`memReal_meet`).

## Main definitions

* `RationalInterval.meet`: the intersection of `I` and `J` when it is nonempty, and `I` otherwise.

## Main results

* `memReal_meet`: a common member of two intervals lies in their meet.

## Implementation notes

`meet` is FloatLib's total intersection `Interval.Exact.intersect`, which returns its first
argument for disjoint intervals. So it needs no overlap proof: `Exact.intersect_lo_le_hi` gives
its endpoint order from that of `I`, and `Exact.containsReal_intersect` gives `memReal_meet`.
`intersect` of `CAS.Continuum.IntervalRefinement` is the same operation with an overlap proof,
from which it states its endpoints. No module of SymLean imports this one; it serves
certificates built on the library.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

open FloatLib.Numerics.Interval

/-- The intersection of `I` and `J` when it is nonempty, and `I` otherwise. -/
def meet (I J : RationalInterval) : RationalInterval :=
  if h : max I.lo J.lo ≤ min I.hi J.hi then
    ofFloatLib (Exact.intersect I.toFloatLib J.toFloatLib) (by
      rw [Exact.intersect_lo, Exact.intersect_hi]
      exact h)
  else I

/-- A common member of two intervals lies in their meet. -/
theorem memReal_meet {I J : RationalInterval} {x : ℝ} (hI : I.MemReal x) (hJ : J.MemReal x) :
    (I.meet J).MemReal x := by
  unfold meet
  split
  · exact ((ofFloatLib _ _).toFloatLib_containsReal_iff x).mp (Exact.containsReal_intersect
      ((I.toFloatLib_containsReal_iff x).mpr hI) ((J.toFloatLib_containsReal_iff x).mpr hJ))
  · exact hI

end CAS.Continuum.RationalInterval
