/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
meta import CAS.Command.Syntax
meta import CAS.Tactic.KernelReadBack

/-!
# The `cas` tactic on integration goals

`cas` proves ordinary Mathlib statements of integration: `HasDerivAt F (f x) x` for a stated
primitive `F`, by the checked derivative route; an interval integral, by Mathlib's closed
formulas or by a primitive whose symbolic derivative is checked and the fundamental theorem of
calculus; and relations with definite integrals. These examples continue `Basic.lean`, which
covers derivatives, the arithmetic route and the identities.
-/

@[expose] public section

namespace CAS.Examples.BasicIntegration

/-! ## Ordinary integration syntax -/

/--
A primitive is stated as an ordinary Mathlib derivative statement: `-cos t` is a primitive of
`sin`. `cas` proves it by the checked derivative route.
-/
example (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ -Real.cos t) (Real.sin x) x := by
  cas

/-- The primitive `cosh` of `sinh`, stated with Mathlib's hyperbolic functions. -/
example (x : ℝ) : HasDerivAt Real.cosh (Real.sinh x) x := by
  cas

/-- The automatically positive denominator `1 + x^2` creates no user condition. -/
example (x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ t * Real.arctan t - Real.log (1 + t ^ 2) / 2)
      (Real.arctan x) x := by
  cas

/-- A primitive of the literal negative power `x ^ (-2 : ℤ)`, under `x ≠ 0`. -/
example (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ -(1 / t)) (x ^ (-2 : ℤ)) x := by
  cas using hx

/-- A primitive of the product `sin x * cos x`. -/
example (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sin t ^ 2 / 2)
      (Real.sin x * Real.cos x) x := by
  cas

/-- A primitive of `sin t ^ 2`, written with the product `cos t * sin t`. -/
example (x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ t / 2 - Real.cos t * Real.sin t / 2)
      (Real.sin x ^ 2) x := by
  cas

/-- An odd power of the sine: the substitution `u = cos t` gives `-cos t + cos t ^ 3 / 3`. -/
example (x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ -Real.cos t + Real.cos t ^ 3 / 3)
      (Real.sin x ^ 3) x := by
  cas

/-- The same primitive at the affine phase `3 t + 2`, divided by its slope `3`. -/
example (x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦
        (-Real.cos (3 * t + 2) + Real.cos (3 * t + 2) ^ 3 / 3) / 3)
      (Real.sin (3 * x + 2) ^ 3) x := by
  cas

/-- An even power of the sine, with the primitive written through that of `sin t ^ 2`. -/
example (x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦
        -(Real.sin t ^ 3 * Real.cos t) / 4 +
          (3 / 4 : ℝ) * (t / 2 - Real.cos t * Real.sin t / 2))
      (Real.sin x ^ 4) x := by
  cas

/-- The primitive `arcsin` of `1 / √(1 - x ^ 2)` needs one interior hypothesis,
`0 < 1 - x ^ 2`. -/
example (x : ℝ) (hinside : 0 < 1 - x ^ 2) :
    HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
  cas using hinside

/-- Sparse powers remain compact enough to certify high-degree primitives. -/
example (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (1 / 101 : ℝ) * t ^ 101) (x ^ 100) x := by
  cas

/--
An ordinary interval integral with symbolic endpoints, which the integration route proves.
-/
example (a b : ℝ) :
    (∫ t in a..b, Real.sin t) = Real.cos a - Real.cos b := by
  cas

/--
Branch-sensitive primitives take ordinary pointwise or interval
hypotheses. The tactic checks these hypotheses against the generated
requirements before using the certificate.
-/
example (a b : ℝ) (hpositive : ∀ t ∈ Set.uIcc a b, 0 < t) :
    (∫ t in a..b, 1 / t) = Real.log b - Real.log a := by
  cas using hpositive

/-- The integration route composes the exact endpoint formula with ordinary bounds. -/
example : (∫ t in (0 : ℝ)..1, Real.sin t) < 10 := by
  cas

/-- Distinct supported integrals are certified independently before arithmetic closure. -/
example :
    (∫ t in (0 : ℝ)..1, t) + (∫ t in (0 : ℝ)..1, t ^ 2) = 5 / 6 := by
  cas

/-! The checked integrator keeps the factors of degree at most two of a rational denominator and
splits `x` off a factor of degree three or more, again while the rest has degree three or more
and `x` divides it (`1 / (x ^ 3 + x)` and `1 / (x ^ 5 + x ^ 3)` in `CAS/Examples/Algebra.lean`).
The denominator `x ^ 3 - 1` has no factor `x`. The integrator leaves the cubic whole and
refuses `1 / (x ^ 3 - 1)`. -/

set_option linter.hashCommand false in
/-- The denominator has a factor of degree three or more that the integrator could not split -/
#guard_msgs (error, drop info, substring := true) in
#cas [integrate x] (1/(x^3 - 1))

end CAS.Examples.BasicIntegration
