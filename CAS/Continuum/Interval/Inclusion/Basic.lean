/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
public import CAS.Continuum.Interval.Elementary.Exp
public import CAS.Continuum.Interval.Elementary.Log
public import CAS.Continuum.Interval.Elementary.Sqrt
public import FloatLib.Numerics.Enclosure.Expression.ElementaryTable
public import FloatLib.Numerics.Enclosure.Expression.Standard
public import FloatLib.Numerics.Enclosure.Interval.Exact
public import Mathlib.Tactic.Inclusion.Core.Extensions
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# FloatLib's ranges on dyadic intervals

Mathlib's `dyadic_interval` tactic evaluates a real expression over `Inclusion.Interval Dyadic`
and checks the result in the kernel. To use FloatLib's interval enclosures there, we register the
`cega_real` family. We read a bounded dyadic interval's endpoints as rationals, apply a FloatLib
enclosure on `FloatLib.Numerics.Interval ℚ`, and round the result outward to dyadic endpoints.
The `prec` parameter sets the rounding grid, as it does for rational literals in
`dyadic_interval`, and also the accuracy of the enclosures (`settings`).

An `inclusion` operation cannot carry side conditions, so every lifted range is total. An
unbounded argument, or an argument the enclosure declines (a reciprocal across zero, say),
produces a fallback interval that holds for every real input.

## Main definitions

* `liftUnary`: a FloatLib enclosure `Interval ℚ → Option (Interval ℚ)` on dyadic intervals.
* `settings prec`, `liftElementary`: the settings of FloatLib's elementary table
  `Backend.elementaryWith` at precision `prec`, and the table lifted with them.
* `invRange?`: FloatLib's exact reciprocal on an interval that excludes zero.

## Main results

* `mem_liftUnary`: the inclusion property of every lifted range.

## Implementation notes

The method is the inclusion principle of interval arithmetic: replacing every operation of an
expression by an interval operation with the inclusion property gives an interval that contains
the value of the expression (Rump, (5.17)). Mathlib's `inclusion` framework builds the interval
expression together with the membership proof, and the kernel decides the goal by evaluating it.
The family, the round trip through rational intervals and the fallbacks are ours. The round trip
adds an outward rounding per operation and lets each operation use FloatLib's enclosure and its
containment theorem unchanged. `dyadic_interval` also evaluates the interval expression before
the kernel checks it, so everything the ranges compute is defined here, in the module that
`CAS.Continuum.Interval.Inclusion.Elementary` imports with `meta`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We use its elementary
  table, its exact reciprocal and power, and its enclosure of `π`.
* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.5 for the inclusion property (5.16) and the inclusion principle (5.17).
-/

@[expose] public section

open Inclusion
open Inclusion.IntervalDyadicReal (Dyadic.toReal)

namespace CAS.Continuum.CEGAInclusion

/-- The `cega_real` inclusion family: FloatLib's certified ranges on Mathlib's dyadic intervals. -/
meta initialize cegaRealFamily : InclusionFamily ← registerInclusionFamily `cega_real

/-- The rational interval with the endpoints of a bounded dyadic interval, `none` for an
unbounded one. -/
def toRational? (I : Interval Dyadic) : Option (FloatLib.Numerics.Interval ℚ) :=
  match (I.lb : Option Dyadic), (I.ub : Option Dyadic) with
  | some a, some b => some ⟨a.toRat, b.toRat⟩
  | _, _ => none

/-- If `x` lies in the dyadic interval `I` and `toRational? I = some J`, then `x` lies in the
rational interval `J`. -/
theorem containsReal_of_toRational? {I : Interval Dyadic} {J : FloatLib.Numerics.Interval ℚ}
    {x : ℝ} (hx : x ∈ I) (hJ : toRational? I = some J) : J.ContainsReal some x := by
  obtain ⟨_ | a, _ | b⟩ := I <;> simp only [toRational?, reduceCtorEq, Option.some.injEq] at hJ
  subst hJ
  rw [IntervalDyadicReal.mem_iff_mem_map, Interval.mem_map_iff] at hx
  exact (FloatLib.Numerics.Interval.containsReal_some_iff _ _).mpr ⟨hx.1 a rfl, hx.2 b rfl⟩

/-- Round a rational interval outward to dyadic endpoints with precision `2 ^ (-prec)`. -/
def ofRational (J : FloatLib.Numerics.Interval ℚ) (prec : ℕ) : Interval Dyadic :=
  Interval.Icc (IntervalDyadicReal.rat J.lo prec).lb (IntervalDyadicReal.rat J.hi prec).ub

/-- Outward rounding keeps members: if `x` lies in the rational interval `J`, it lies in the
dyadic interval `ofRational J prec`, for every precision `prec`. -/
theorem mem_ofRational {J : FloatLib.Numerics.Interval ℚ} {x : ℝ} (hx : J.ContainsReal some x)
    (prec : ℕ) : x ∈ ofRational J prec := by
  obtain ⟨hlo, hhi⟩ := (FloatLib.Numerics.Interval.containsReal_some_iff J x).mp hx
  exact Interval.mem_Icc_of_le (IntervalDyadicReal.ratCast_mem J.lo prec) hlo hhi
    (IntervalDyadicReal.ratCast_mem J.hi prec)

/--
Lift a FloatLib enclosure `f` to dyadic intervals.

A bounded argument goes through `f` and is rounded outward; an unbounded argument, or one on
which `f` returns `none`, gives `fallback`.
-/
def liftUnary (f : FloatLib.Numerics.Interval ℚ → Option (FloatLib.Numerics.Interval ℚ))
    (fallback : Interval Dyadic) (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match (toRational? I).bind f with
  | some K => ofRational K prec
  | none => fallback

/-- If `f` encloses `g` on rational intervals and `fallback` contains every value of `g`,
then the lifted range encloses `g` on dyadic intervals. -/
theorem mem_liftUnary {g : ℝ → ℝ}
    {f : FloatLib.Numerics.Interval ℚ → Option (FloatLib.Numerics.Interval ℚ)}
    (hf : ∀ {J K : FloatLib.Numerics.Interval ℚ} {x : ℝ}, f J = some K →
      J.ContainsReal some x → K.ContainsReal some (g x))
    {fallback : Interval Dyadic} (hfallback : ∀ x, g x ∈ fallback)
    {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    g x ∈ liftUnary f fallback I prec := by
  unfold liftUnary
  cases hI : toRational? I with
  | none => exact hfallback x
  | some J =>
    cases hK : f J with
    | none => simpa [hK] using hfallback x
    | some K => simpa [hK] using mem_ofRational (hf hK (containsReal_of_toRational? hx hI)) prec

/-- The Taylor order of the exponential and the hyperbolic functions at precision `prec`,
`max defaultExpTaylorOrder (prec / 2)`, so that small precisions keep the default order of
`expRange`. -/
def taylorOrder (prec : ℕ) : ℕ := max RationalInterval.defaultExpTaylorOrder (prec / 2)

/--
The settings of FloatLib's elementary table for the `cega_real` ranges at precision `prec`.

The exponential and the hyperbolic functions have Taylor degree `taylorOrder prec`, the logarithm
has `max logSeriesTerms (prec / 2)` series terms, and the square root keeps
`max defaultSqrtRefinementSteps (prec + 4)` binary digits. Sine and cosine are the sharp
enclosures at Taylor degree `32` on a 128-bit grid, the arctangent has degree `16`, and the
inverse sine and cosine have degree `32`. The square root, the logarithm and the inverse sine and
cosine follow Mathlib's total functions (`total`).
-/
def settings (prec : ℕ) : FloatLib.Numerics.Interval.ElementarySettings where
  expDegree := taylorOrder prec
  logDegree := RationalInterval.logFloatLibDegree (max RationalInterval.logSeriesTerms (prec / 2))
  trigDegree := 32
  atanDegree := 16
  inverseTrigDegree := 32
  hyperbolicDegree := taylorOrder prec
  precision := max RationalInterval.defaultSqrtRefinementSteps (prec + 4)
  sharpTrig := some 128
  total := true

/-- The enclosure of the elementary operation `op` from FloatLib's table at the settings
`settings prec`, lifted to dyadic intervals with `liftUnary`. -/
def liftElementary (op : FloatLib.Numerics.Interval.UnaryOp) (fallback : Interval Dyadic)
    (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  liftUnary (FloatLib.Numerics.Interval.Backend.elementaryWith (settings prec) op) fallback I prec

/-- FloatLib's exact reciprocal `Interval.Exact.inv` on an interval that lies strictly on one side
of zero; `none` on an interval that contains zero. -/
def invRange? (J : FloatLib.Numerics.Interval ℚ) : Option (FloatLib.Numerics.Interval ℚ) :=
  if J.hi < 0 ∨ 0 < J.lo then some (FloatLib.Numerics.Interval.Exact.inv J) else none

/-- The dyadic interval `[lo, hi]`. -/
def closed (lo hi : Dyadic) : Interval Dyadic := Interval.Icc lo hi

/-- A real `x` with `lo ≤ x ≤ hi` (endpoints read as reals) lies in the dyadic interval
`closed lo hi`. -/
theorem mem_closed {lo hi : Dyadic} {x : ℝ} (hlo : Dyadic.toReal lo ≤ x)
    (hhi : x ≤ Dyadic.toReal hi) :
    x ∈ closed lo hi :=
  Interval.mem_map_Icc Dyadic.toReal hlo hhi

/-- The dyadic interval `[lo, ∞)`. -/
def atLeast (lo : Dyadic) : Interval Dyadic := Interval.Ici lo

/-- A real `x` with `lo ≤ x` (`lo` read as a real) lies in the dyadic interval `atLeast lo`. -/
theorem mem_atLeast {lo : Dyadic} {x : ℝ} (hlo : Dyadic.toReal lo ≤ x) : x ∈ atLeast lo :=
  ⟨WithBot.coe_le_coe.mpr hlo, le_top⟩

end CAS.Continuum.CEGAInclusion
