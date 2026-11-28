/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.ElementaryTable

/-!
# Precision policy for certified evaluation

A CEGA query carries one `Precision` policy through the registry planner: the Taylor order of
the exponential and hyperbolic functions, the number of logarithm series terms, the binary digits
of square roots, the subdivision depth of checked box refinement, and an optional number of
decimal digits.

The certified evaluation context computes with FloatLib. `Precision.toSetting` is the setting of
FloatLib's elementary table for a policy, and `Precision.toConfig` the accuracy settings of the
registered calls of a translated expression, `π`, the real power and `e`.

Precision is planner data. Every enclosure theorem holds for all settings, so the policy affects
the sharpness and the cost of an enclosure but never its soundness.

Only the exponential, hyperbolic, logarithm and square-root ranges, the real power and the
subdivision depth read the policy. Sine and cosine use 32 terms and FloatLib's sharp enclosures,
the inverse trigonometric functions fixed degrees, and `π` and `e` 128 bits, so a larger policy
need not sharpen them. A `digits` request makes box enclosures try `DigitsEval.eval` first, whose
precision covers those functions too.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/--
Numerical precision policy for automatic interval compilation.

The defaults use exponential Taylor order 8, square roots with 12 binary digits, 10 logarithm
series terms, and subdivision depth 2.
-/
structure Precision where
  /-- Taylor order for exponential and hyperbolic ranges; zero is promoted to one. -/
  expOrder : ℕ := 8
  /-- Binary digits of square-root enclosures. -/
  sqrtDigits : ℕ := 12
  /-- Series terms for logarithm ranges, run by FloatLib at degree `2 * max logTerms 1`. -/
  logTerms : ℕ := 10
  /-- Number of checked bisection levels used by subdivided enclosures. -/
  depth : ℕ := 2
  /-- Requested decimal digits. When set, box enclosures first try the precision-parametric
  evaluator `DigitsEval.eval` at the working precision `DigitsEval.precisionFor digits`. -/
  digits : Option ℕ := none
deriving Repr, DecidableEq

namespace Precision

/--
The policy that requests the Taylor order `prec` for `exp`, `prec` series terms for
`log`, and `prec` binary digits for square roots, keeping the subdivision depth and
the `digits` request.
-/
def withPrec (policy : Precision) (prec : ℕ) : Precision :=
  { policy with expOrder := prec, sqrtDigits := prec, logTerms := prec }

/-- The policy with a requested subdivision depth. -/
def withDepth (policy : Precision) (depth : ℕ) : Precision :=
  { policy with depth := depth }

/--
The setting of FloatLib's elementary table for this policy.

The exponential and the hyperbolic functions run at the degree `max expOrder 1`, the logarithm
at `2 * max logTerms 1`, and square roots with `sqrtDigits` binary digits. Sine and cosine use 32
terms and FloatLib's sharp enclosures on monotone panels, rounded to a grid of `2 ^ (-128)`. The
arctangent runs at the degree 16, and the arcsine and arccosine at the degree 32. Square root,
arcsine, arccosine and logarithm follow Mathlib's total functions (`total`), and no exponential
or logarithm is rounded to a binary grid.
-/
def toSetting (policy : Precision) : FloatLib.Numerics.Interval.ElementarySettings where
  expDegree := max policy.expOrder 1
  logDegree := 2 * max policy.logTerms 1
  trigDegree := 32
  atanDegree := 16
  inverseTrigDegree := 32
  hyperbolicDegree := max policy.expOrder 1
  precision := policy.sqrtDigits
  sharpTrig := some 128
  total := true
  gridExpLog := none

/--
The accuracy settings of FloatLib's registered calls for this policy. `π` and `e` get 128 bits,
and the real power, which evaluates `exp (log a * b)` at one degree, the larger of the exponential
and logarithm degrees of `toSetting`.
-/
def toConfig (policy : Precision) : FloatLib.Numerics.Interval.Backend.Config where
  precision := 128
  degree := max (max policy.expOrder 1) (2 * max policy.logTerms 1)

end Precision

end RationalInterval
end CAS.Continuum
